module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# A criterion for representability of group-valued functors

A Zariski sheaf of groups over a field is represented by a group scheme if it has a representable
open subfunctor whose translates by rational points meet every point over a field extension.

## Main definitions

* `AlgebraicGeometry.fieldExtensionPoint`: the spectrum of a field extension, viewed as a scheme
  over the ground field.

## Main results

* `AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor`: the representing group
  scheme.

## Implementation notes

The group scheme is expressed as a group object in schemes over `Spec k`, and the representing
isomorphism is an isomorphism of group-valued functors.  The open subfunctor is a subfunctor of
the underlying type-valued functor.

The proof passes to the *total* functor on all schemes, whose sections over a scheme `T` are
pairs consisting of a structural morphism `T ⟶ Spec k` and a section of `G` over `T` seen as a
scheme over `Spec k`.  That functor is a Zariski sheaf, the translates of the given open
subfunctor give it an open cover by representable subfunctors, and Mathlib's local
representability criterion applies; representability of the total functor is then transferred
back to `G`.  The transfer in both directions is the content of the private lemmas
`totalPresheaf_isSheaf` and `representableOver_of_totalRepresentable`.

Because the fibre of the total functor over a structural morphism `f` is `G` evaluated at
`Over.mk f`, comparing two sections involves transporting along equalities of objects of the
slice category; this is why the proofs below carry `eqToHom` transports and heterogeneous
equalities, isolated through `cast_eqToHom_apply`.

## References

* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The spectrum of a field extension, as a scheme over the ground field. -/
noncomputable abbrev fieldExtensionPoint (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))

private noncomputable def totalPresheafMap (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u) {X Y : Schemeᵒᵖ} (α : X ⟶ Y) :
    (Σ f : unop X ⟶ Spec (.of k), G.obj (op (Over.mk f))) ⟶
      (Σ f : unop Y ⟶ Spec (.of k), G.obj (op (Over.mk f))) :=
  ↾fun x =>
    let a : unop Y ⟶ unop X := α.unop
    let b : unop Y ⟶ Spec (.of k) := a ≫ x.1
    let h : Over.mk b ⟶ Over.mk x.1 := Over.homMk a
    ⟨b, G.map h.op x.2⟩

/-- The total presheaf of a presheaf on schemes over `Spec k`.
Its sections remember both the structural map to the base and the relative section. -/
private noncomputable def totalPresheaf (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u) : Schemeᵒᵖ ⥤ Type u where
  obj X := Σ f : X.unop ⟶ Spec (.of k), G.obj (op (Over.mk f))
  map α := totalPresheafMap k G α
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    dsimp [totalPresheafMap]
    apply Sigma.ext
    · simp
    · have h : (𝟙 (unop X)) ≫ x.1 = x.1 := by simp
      cases h
      apply heq_of_eq
      change G.map (Over.homMk (𝟙 (unop X))).op x.2 = x.2
      rw [show (Over.homMk (𝟙 (unop X)) : Over.mk x.1 ⟶ Over.mk x.1) = 𝟙 _ by
        ext
        simp]
      simp
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro x
    dsimp [totalPresheafMap]
    apply Sigma.ext
    · simp [Category.assoc]
    · have h : β.unop ≫ (α.unop ≫ x.1) = (β.unop ≫ α.unop) ≫ x.1 := by
        simp [Category.assoc]
      cases h
      apply heq_of_eq
      rw [← Functor.map_comp_apply]
      congr 1

private noncomputable def totalPresheafBase (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u) :
    totalPresheaf k G ⟶ yoneda.obj (Spec (.of k)) where
  app X := ↾fun x => x.1
  naturality := by
    intro X Y f
    ext x
    rfl

private lemma cast_eqToHom_apply {α β : Type u} (h : α = β) (x : α) :
    cast h x = (ConcreteCategory.hom (eqToHom h)) x := by
  cases h
  rfl

/-- Heterogeneous equality of sections across an equality of objects, as an equation of
transports. -/
private lemma heq_iff_eq_map_eqToHom {C : Type*} [Category C] (G : Cᵒᵖ ⥤ Type u) {X Y : C}
    (e : X = Y) (x : G.obj (op X)) (y : G.obj (op Y)) :
    x ≍ y ↔ x = G.map (eqToHom e).op y := by
  have hc : cast (congrArg (fun Z => G.obj (op Z)) e).symm y = G.map (eqToHom e).op y := by
    simpa only [eqToHom_op, eqToHom_map] using cast_eqToHom_apply _ y
  rw [heq_iff_exists_eq_cast]
  exact ⟨fun ⟨_, hx⟩ => hx.trans hc, fun hx => ⟨_, hx.trans hc.symm⟩⟩

/-- Pulling back a transported section along a morphism of the slice category agrees, up to
transport, with pulling it back along the underlying morphism. -/
private lemma map_op_eqToHom_heq_map_homMk {k : Type u} [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u) {U₀ V₀ : Scheme.{u}}
    {fU : U₀ ⟶ Spec (.of k)} {fV : V₀ ⟶ Spec (.of k)} (g : Over.mk fV ⟶ Over.mk fU)
    {s : U₀ ⟶ Spec (.of k)} (hu : fU = s) (z : G.obj (op (Over.mk s))) :
    G.map g.op (G.map (eqToHom (congrArg Over.mk hu)).op z) ≍
      G.map (Over.homMk g.left : Over.mk (g.left ≫ s) ⟶ Over.mk s).op z := by
  have hv : fV = g.left ≫ s := (Over.w g).symm.trans (congrArg (g.left ≫ ·) hu)
  have hm : eqToHom (congrArg Over.mk hv) ≫ (Over.homMk g.left : Over.mk (g.left ≫ s) ⟶ Over.mk s) =
      g ≫ eqToHom (congrArg Over.mk hu) := by
    apply Over.OverMorphism.ext
    simp [Over.comp_left]
  rw [heq_iff_eq_map_eqToHom G (congrArg Over.mk hv), ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, ← op_comp, ← op_comp, hm]

private theorem totalPresheaf_isSheaf (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u)
    (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (.of k))) G) :
    Presieve.IsSheaf Scheme.zariskiTopology (totalPresheaf k G) := by
  intro X R hR x hx
  have hbase : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj (Spec (.of k))) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let xb := x.map (totalPresheafBase k G)
  have hxb : xb.Compatible := hx.map (totalPresheafBase k G)
  obtain ⟨f, hf, hfuniq⟩ := hbase R hR xb hxb
  let Y : Over (Spec (.of k)) := Over.mk f
  let R' : Sieve Y := (Sieve.overEquiv Y).symm R
  have hR' : R' ∈ (Scheme.zariskiTopology.over (Spec (.of k))) Y := by
    apply Scheme.zariskiTopology.overEquiv_symm_mem_over
    exact hR
  have hleft {Z : Over (Spec (.of k))} {a : Z ⟶ Y} (ha : R'.arrows a) : R a.left :=
    (Sieve.overEquiv_symm_iff R a).1 ha
  have hfst {Z : Scheme.{u}} {a : Z ⟶ X} (ha : R a) : (x a ha).1 = a ≫ f := by
    simpa [xb, totalPresheafBase] using (hf a ha).symm
  let y : R'.arrows.FamilyOfElements G := fun Z a ha => by
    cases Z with
    | mk Z0 _ fZ =>
      let s := x a.left (hleft ha)
      have hs : s.1 = fZ := (hfst (hleft ha)).trans (Over.w a)
      exact G.map (eqToHom (congrArg Over.mk hs.symm)).op s.2
  have hy : y.Compatible := by
    intro U₁ U₂ V g₁ g₂ a₁ a₂ h₁ h₂ comm
    cases U₁ with
    | mk U₁₀ _ f₁ =>
    cases U₂ with
    | mk U₂₀ _ f₂ =>
    cases V with
    | mk V₀ _ fV =>
    have htot := hx g₁.left g₂.left (hleft h₁) (hleft h₂)
      (by simpa [← Over.comp_left] using congrArg Over.Hom.left comm)
    let s₁ := x a₁.left (hleft h₁)
    let s₂ := x a₂.left (hleft h₂)
    have hu₁ : f₁ = s₁.1 := (Over.w a₁).symm.trans (hfst (hleft h₁)).symm
    have hu₂ : f₂ = s₂.1 := (Over.w a₂).symm.trans (hfst (hleft h₂)).symm
    have hv₁ : fV = g₁.left ≫ s₁.1 :=
      (Over.w g₁).symm.trans (congrArg (fun q => g₁.left ≫ q) hu₁)
    have hv₂ : fV = g₂.left ≫ s₂.1 :=
      (Over.w g₂).symm.trans (congrArg (fun q => g₂.left ≫ q) hu₂)
    have hsec₁ : G.map g₁.op (y a₁ h₁) ≍ (totalPresheafMap k G g₁.left.op s₁).2 := by
      rw [show y a₁ h₁ = G.map (eqToHom (congrArg Over.mk hu₁)).op s₁.2 by simp [y, s₁]]
      exact map_op_eqToHom_heq_map_homMk G g₁ hu₁ s₁.2
    have hsec₂ : G.map g₂.op (y a₂ h₂) ≍ (totalPresheafMap k G g₂.left.op s₂).2 := by
      rw [show y a₂ h₂ = G.map (eqToHom (congrArg Over.mk hu₂)).op s₂.2 by simp [y, s₂]]
      exact map_op_eqToHom_heq_map_homMk G g₂ hu₂ s₂.2
    change (totalPresheafMap k G g₁.left.op s₁) =
      (totalPresheafMap k G g₂.left.op s₂) at htot
    have hsec : (totalPresheafMap k G g₁.left.op s₁).2 ≍
        (totalPresheafMap k G g₂.left.op s₂).2 := (Sigma.ext_iff.mp htot).2
    exact eq_of_heq (hsec₁.trans (hsec.trans hsec₂.symm))
  obtain ⟨g, hg, hgunique⟩ := hG R' hR' y hy
  refine ⟨⟨f, g⟩, ?_, ?_⟩
  · intro Z a ha
    apply Sigma.ext
    · exact hf a ha
    · let s := x a ha
      have hs : s.1 = a ≫ f := hfst ha
      let eU : Over.mk (a ≫ f) = Over.mk s.1 := congrArg Over.mk hs.symm
      let q : Over.mk (a ≫ f) ⟶ Y := Over.homMk a
      have hq : R'.arrows q :=
        (Sieve.overEquiv_symm_iff R q).2 ha
      refine (heq_iff_eq_map_eqToHom G eU _ _).2 ?_
      exact hg q hq
  · intro t ht
    rcases t with ⟨f', g'⟩
    have hf' : xb.IsAmalgamation f' := by
      intro Z a ha
      have hfst := congrArg Sigma.fst (ht a ha)
      change a ≫ f' = (x a ha).1 at hfst
      simpa [xb, totalPresheafBase] using hfst
    have hff : f' = f := hfuniq f' hf'
    cases hff
    show (⟨f, g'⟩ : (totalPresheaf k G).obj (op X)) = ⟨f, g⟩
    apply congrArg (fun z : G.obj (op Y) => (⟨f, z⟩ : (totalPresheaf k G).obj (op X)))
    apply hgunique g'
    intro Z q hq
    cases Z with
    | mk Z₀ _ fZ =>
      have ha : R.arrows q.left := hleft hq
      let s := x q.left ha
      have hs : s.1 = q.left ≫ f := hfst ha
      have hu : fZ = s.1 := (Over.w q).symm.trans hs.symm
      let eU : Over.mk fZ = Over.mk s.1 := congrArg Over.mk hu
      let eV : Over.mk (q.left ≫ f) = Over.mk fZ := congrArg Over.mk (Over.w q)
      let eT : Over.mk (q.left ≫ f) = Over.mk s.1 := eV.trans eU
      let m : Over.mk (q.left ≫ f) ⟶ Y := Over.homMk q.left
      have hm : m = eqToHom eV ≫ q := by
        apply Over.OverMorphism.ext
        simp [m, Over.comp_left]
      have htq := ht q.left ha
      dsimp [totalPresheaf] at htq
      have hsec := (Sigma.ext_iff.mp htq).2
      change (G.map m.op).hom g' ≍ s.2 at hsec
      have hsecEq := (heq_iff_eq_map_eqToHom G eT _ _).1 hsec
      have hleft : (G.map m.op).hom g' =
          (G.map (eqToHom eV).op).hom ((G.map q.op).hom g') := by
        rw [hm]
        simp only [op_comp, Functor.map_comp_apply]
      have hright : (G.map (eqToHom eT).op).hom s.2 =
          (G.map (eqToHom eV).op).hom ((G.map (eqToHom eU).op).hom s.2) := by
        have hteq : eqToHom eT = eqToHom eV ≫ eqToHom eU := by simp
        rw [hteq]
        simp only [op_comp, Functor.map_comp_apply]
      have hcancel : (G.map (eqToHom eV).op).hom ((G.map q.op).hom g') =
          (G.map (eqToHom eV).op).hom ((G.map (eqToHom eU).op).hom s.2) :=
        hleft.symm.trans (hsecEq.trans hright)
      have hinj : Function.Injective ((G.map (eqToHom eV).op).hom) :=
        (ConcreteCategory.bijective_of_isIso (G.map (eqToHom eV).op)).1
      show (G.map q.op).hom g' = (G.map (eqToHom eU).op).hom s.2
      exact hinj hcancel

private noncomputable def totalChart (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (F : Subfunctor (G ⋙ forget GrpCat)) (Y : Over (Spec (.of k)))
    (e : yoneda.obj Y ≅ F.toFunctor) :
    yoneda.obj Y.left ⟶ totalPresheaf k (G ⋙ forget GrpCat) where
  app X := ↾fun f =>
    let m : Over.mk (f ≫ Y.hom) ⟶ Y := Over.homMk f
    ⟨f ≫ Y.hom, F.ι.app _ (e.hom.app _ m)⟩
  naturality := by
    intro X X' α
    ext f
    dsimp [totalPresheaf, totalPresheafMap]
    apply Sigma.ext
    · simp [Category.assoc]
    · apply heq_of_eq
      let m : Over.mk ((α.unop ≫ f) ≫ Y.hom) ⟶ Over.mk (f ≫ Y.hom) := Over.homMk α.unop
      let n : Over.mk (f ≫ Y.hom) ⟶ Y := Over.homMk f
      have hcomp :
          (Over.homMk (α.unop ≫ f) : Over.mk ((α.unop ≫ f) ≫ Y.hom) ⟶ Y) = m ≫ n := by
        apply Over.OverMorphism.ext
        simp [m, n, Over.comp_left]
      rw [hcomp]
      exact F.nat_trans_naturality e.hom m.op n

private noncomputable def totalTranslation (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (r : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
    totalPresheaf k (G ⋙ forget GrpCat) ⟶ totalPresheaf k (G ⋙ forget GrpCat) where
  app X := ↾fun x =>
    let h : Over.mk x.1 ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk x.1
    ⟨x.1, ((G ⋙ forget GrpCat).map h.op) r * x.2⟩
  naturality := by
    intro X X' α
    ext x
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      let a : unop X' ⟶ unop X := α.unop
      let q : Over.mk (a ≫ x.1) ⟶ Over.mk x.1 := Over.homMk a
      let h₁ : Over.mk x.1 ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk x.1
      let h₂ : Over.mk (a ≫ x.1) ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk (a ≫ x.1)
      have hcomp : h₂ = q ≫ h₁ := by
        apply Over.OverMorphism.ext
        simp [q, h₁, h₂, Over.comp_left]
      let x₂ : ↑(G.obj (op (Over.mk x.1))) := x.2
      change (G.map h₂.op).hom r * (G.map q.op).hom x₂ =
        (G.map q.op).hom ((G.map h₁.op).hom r * x₂)
      calc
        (G.map h₂.op).hom r * (G.map q.op).hom x₂ =
            (G.map q.op).hom ((G.map h₁.op).hom r) * (G.map q.op).hom x₂ := by
          rw [hcomp]
          simp only [op_comp, Functor.map_comp_apply]
        _ = (G.map q.op).hom ((G.map h₁.op).hom r * x₂) := by rw [map_mul]

private noncomputable def totalTranslatedChart (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (F : Subfunctor (G ⋙ forget GrpCat)) (Y : Over (Spec (.of k)))
    (e : yoneda.obj Y ≅ F.toFunctor)
    (r : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
    yoneda.obj Y.left ⟶ totalPresheaf k (G ⋙ forget GrpCat) :=
  totalChart k G F Y e ≫ totalTranslation k G r⁻¹

private theorem totalTranslation_inv_apply (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (r : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) (X : Schemeᵒᵖ)
    (x : (totalPresheaf k (G ⋙ forget GrpCat)).obj X) :
    (totalTranslation k G r).app X ((totalTranslation k G r⁻¹).app X x) = x := by
  apply Sigma.ext
  · rfl
  · dsimp [totalTranslation]
    apply heq_of_eq
    let h : Over.mk x.1 ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk x.1
    let φ := G.map h.op
    let z : ↑(G.obj (op (Over.mk x.1))) := x.2
    show φ.hom' r * (φ.hom' r⁻¹ * z) = z
    rw [φ.hom'.map_inv, mul_inv_cancel_left]

private theorem totalChart_naturality_from_section (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (F : Subfunctor (G ⋙ forget GrpCat))
    (T : Scheme.{u}) (b : T ⟶ Spec (.of k))
    (W : Over (Spec (.of k)))
    (u : yoneda.obj W ⟶ F.toFunctor)
    (v : yoneda.obj W ⟶ yoneda.obj (Over.mk b))
    (x : (G ⋙ forget GrpCat).obj (op (Over.mk b)))
    (h : (F.ι.app (op W)).hom ((u.app (op W)).hom (𝟙 W)) =
      ((v ≫ yonedaEquiv.symm x).app (op W)).hom (𝟙 W)) :
    u ≫ F.ι = v ≫ yonedaEquiv.symm x :=
  yonedaEquiv.injective h

private theorem totalChart_pullback_lift (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (F : Subfunctor (G ⋙ forget GrpCat))
    (Y : Over (Spec (.of k))) (e : yoneda.obj Y ≅ F.toFunctor)
    (T : Scheme.{u}) (b : T ⟶ Spec (.of k))
    (x : (G ⋙ forget GrpCat).obj (op (Over.mk b)))
    (P : Over (Spec (.of k))) (snd : P ⟶ Over.mk b)
    (fst : yoneda.obj P ⟶ F.toFunctor)
    (hPB : IsPullback fst (yoneda.map snd) F.ι (yonedaEquiv.symm x))
    (uOver : P ⟶ Y) (huYoneda : yoneda.map uOver = fst ≫ e.inv)
    (W : Over (Spec (.of k))) (i : W ⟶ Y) (j : W ⟶ Over.mk b)
    (hcompat : (F.ι.app (op W)).hom ((e.hom.app (op W)).hom i) =
      ((G ⋙ forget GrpCat).map j.op).hom x) :
    ∃ a : W ⟶ P, a ≫ uOver = i ∧ a ≫ snd = j := by
  let gOver : yoneda.obj (Over.mk b) ⟶ G ⋙ forget GrpCat := yonedaEquiv.symm x
  let v : yoneda.obj W ⟶ yoneda.obj (Over.mk b) := yoneda.map j
  let f : yoneda.obj W ⟶ F.toFunctor := yonedaEquiv.symm ((e.hom.app (op W)).hom i)
  have hf0 : (f.app (op W)).hom (𝟙 W) = (e.hom.app (op W)).hom i := by
    show (F.toFunctor.map (𝟙 W).op).hom ((e.hom.app (op W)).hom i) = _
    exact F.toFunctor.map_id_apply (op W) ((e.hom.app (op W)).hom i)
  have hnat : f ≫ F.ι = v ≫ gOver := by
    apply totalChart_naturality_from_section k G F T b W f v x
    show (F.ι.app (op W)).hom ((f.app (op W)).hom (𝟙 W)) = ((yonedaEquiv.symm x).app (op W)).hom j
    calc
      (F.ι.app (op W)).hom ((f.app (op W)).hom (𝟙 W)) =
          (F.ι.app (op W)).hom ((e.hom.app (op W)).hom i) :=
        congrArg ((F.ι.app (op W)).hom) hf0
      _ = ((G ⋙ forget GrpCat).map j.op).hom x := hcompat
      _ = ((yonedaEquiv.symm x).app (op W)).hom j :=
        (yonedaEquiv_symm_app_apply x (op W) j).symm
  let ℓ := hPB.lift f v hnat
  let a : W ⟶ P := yonedaEquiv ℓ
  have hya : yoneda.map a = ℓ := by
    apply yonedaEquiv.injective
    show yonedaEquiv (yoneda.map a) = yonedaEquiv ℓ
    rw [yonedaEquiv_yoneda_map]
  have haSnd : a ≫ snd = j := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hya]
    exact hPB.lift_snd f v hnat
  have haFst : ℓ ≫ fst = f := hPB.lift_fst f v hnat
  have haY : a ≫ uOver = i := by
    apply yoneda.map_injective
    have hui : f ≫ e.inv = yoneda.map i := by
      apply yonedaEquiv.injective
      show yonedaEquiv (f ≫ e.inv) = yonedaEquiv (yoneda.map i)
      rw [yonedaEquiv_yoneda_map]
      show ((f ≫ e.inv).app (op W)).hom (𝟙 W) = i
      have hi' : (e.inv.app (op W)).hom ((e.hom.app (op W)).hom i) = i := by
        simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
          ConcreteCategory.congr_hom (e.hom_inv_id_app (op W)) i
      calc
        ((f ≫ e.inv).app (op W)).hom (𝟙 W) =
            (e.inv.app (op W)).hom ((f.app (op W)).hom (𝟙 W)) := by
          simp only [NatTrans.comp_app_apply]
        _ = (e.inv.app (op W)).hom ((e.hom.app (op W)).hom i) :=
          congrArg ((e.inv.app (op W)).hom) hf0
        _ = i := hi'
    calc
      yoneda.map (a ≫ uOver) = ℓ ≫ fst ≫ e.inv := by
        rw [Functor.map_comp, hya, ← huYoneda]
      _ = f ≫ e.inv := by
        simpa [← Category.assoc] using congrArg (fun z => z ≫ e.inv) haFst
      _ = yoneda.map i := hui
  exact ⟨a, haY, haSnd⟩

-- The pullback construction involves repeated transports between objects of the slice category.
private theorem totalTranslatedChart_isOpenImmersion (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (F : Subfunctor (G ⋙ forget GrpCat))
    (Y : Over (Spec (.of k))) (e : yoneda.obj Y ≅ F.toFunctor)
    (r : G.obj (op (Over.mk (𝟙 (Spec (.of k))))))
    (hopen : (IsOpenImmersion.over (X := Spec (.of k))).presheaf F.ι) :
    IsOpenImmersion.presheaf (totalTranslatedChart k G F Y e r) := by
  apply MorphismProperty.relative.of_exists
  intro T q
  let qR := yonedaEquiv (q ≫ totalTranslation k G r)
  let b := qR.1
  let x := qR.2
  let gOver : yoneda.obj (Over.mk b) ⟶ G ⋙ forget GrpCat := yonedaEquiv.symm x
  obtain ⟨P, snd, fst, hPB⟩ := hopen.rep gOver
  let uOver : P ⟶ Y := yonedaEquiv (fst ≫ e.inv)
  let chartMap : yoneda.obj P.left ⟶ yoneda.obj Y.left := yoneda.map uOver.left
  let baseMap : yoneda.obj P.left ⟶ yoneda.obj T := yoneda.map snd.left
  have hopenSnd : IsOpenImmersion.over snd := hopen.property gOver fst snd hPB
  have hOpenLeft : IsOpenImmersion snd.left := hopenSnd
  have hPBval : (F.ι.app (op P)).hom ((fst.app (op P)).hom (𝟙 P)) =
      (gOver.app (op P)) snd := by
    have h := congrArg (fun η => η.app (op P) (𝟙 P)) hPB.w
    have hsnd : ((yoneda.map snd).app (op P)) (𝟙 P) = snd := by simp
    simpa only [NatTrans.comp_app_apply, hsnd] using h
  have hbaseChart : uOver.left ≫ Y.hom = snd.left ≫ b := by
    calc
      uOver.left ≫ Y.hom = P.hom := Over.w uOver
      _ = snd.left ≫ b := (Over.w snd).symm
  let eU : Over.mk (uOver.left ≫ Y.hom) = P := congrArg Over.mk (Over.w uOver)
  let eV : Over.mk (snd.left ≫ b) = P := congrArg Over.mk (Over.w snd)
  have hmU : eqToHom eU ≫ uOver =
      Over.homMk ((eqToHom eU).left ≫ uOver.left) := by
    apply Over.OverMorphism.ext
    simp [Over.comp_left]
  have hmV : eqToHom eV ≫ snd =
      Over.homMk ((eqToHom eV).left ≫ snd.left) := by
    apply Over.OverMorphism.ext
    simp [Over.comp_left]
  have huYoneda : yoneda.map uOver = fst ≫ e.inv := by
    apply yonedaEquiv.injective
    show yonedaEquiv (yoneda.map uOver) = yonedaEquiv (fst ≫ e.inv)
    rw [yonedaEquiv_yoneda_map]
  have huSection : (e.hom.app (op P)) uOver = (fst.app (op P)).hom (𝟙 P) := by
    have hcomp : yoneda.map uOver ≫ e.hom = fst := by
      rw [huYoneda]
      simp
    have h := congrArg (fun η => η.app (op P) (𝟙 P)) hcomp
    simpa using h
  have hmUrev : eqToHom eU.symm ≫
      Over.homMk ((eqToHom eU).left ≫ uOver.left) = uOver := by
    rw [← hmU]
    simp
  have hnatU : F.toFunctor.map (eqToHom eU.symm).op
      ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
        (Over.homMk ((eqToHom eU).left ≫ uOver.left))) =
      (fst.app (op P)).hom (𝟙 P) := by
    calc
      F.toFunctor.map (eqToHom eU.symm).op
          ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
            (Over.homMk ((eqToHom eU).left ≫ uOver.left))) =
          (e.hom.app (op P))
            (eqToHom eU.symm ≫ Over.homMk ((eqToHom eU).left ≫ uOver.left)) :=
        (NatTrans.naturality_apply e.hom (eqToHom eU.symm).op
          (Over.homMk ((eqToHom eU).left ≫ uOver.left))).symm
      _ = (e.hom.app (op P)) uOver := by rw [hmUrev]
      _ = (fst.app (op P)).hom (𝟙 P) := huSection
  have hιU : ((G ⋙ forget GrpCat).map (eqToHom eU.symm).op).hom
      ((F.ι.app (op (Over.mk (uOver.left ≫ Y.hom)))).hom
        ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
          (Over.homMk ((eqToHom eU).left ≫ uOver.left)))) =
      (F.ι.app (op P)).hom ((fst.app (op P)).hom (𝟙 P)) := by
    calc
      _ = (F.ι.app (op P)).hom
          ((F.toFunctor.map (eqToHom eU.symm).op).hom
            ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
              (Over.homMk ((eqToHom eU).left ≫ uOver.left)))) := by
        simpa using (NatTrans.naturality_apply F.ι (eqToHom eU.symm).op
          ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
            (Over.homMk ((eqToHom eU).left ≫ uOver.left)))).symm
      _ = (F.ι.app (op P)).hom ((fst.app (op P)).hom (𝟙 P)) := by rw [hnatU]
  have hnVrev : eqToHom eV.symm ≫
      Over.homMk ((eqToHom eV).left ≫ snd.left) = snd := by
    rw [← hmV]
    simp
  have hnatV : ((G ⋙ forget GrpCat).map (eqToHom eV.symm).op).hom
      ((gOver.app (op (Over.mk (snd.left ≫ b))))
        (Over.homMk ((eqToHom eV).left ≫ snd.left))) =
      (gOver.app (op P)) snd := by
    show ((G ⋙ forget GrpCat).map (eqToHom eV.symm).op).hom
        (((G ⋙ forget GrpCat).map (Over.homMk ((eqToHom eV).left ≫ snd.left)).op).hom x) =
      ((G ⋙ forget GrpCat).map snd.op).hom x
    rw [← Functor.map_comp_apply, ← op_comp, hnVrev]
  have hsectionTransport :
      ((G ⋙ forget GrpCat).map (eqToHom eU.symm).op).hom
          ((F.ι.app (op (Over.mk (uOver.left ≫ Y.hom)))).hom
            ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
              (Over.homMk ((eqToHom eU).left ≫ uOver.left)))) =
        ((G ⋙ forget GrpCat).map (eqToHom eV.symm).op).hom
          ((gOver.app (op (Over.mk (snd.left ≫ b))))
            (Over.homMk ((eqToHom eV).left ≫ snd.left))) :=
    hιU.trans (hPBval.trans hnatV.symm)
  let eUV : Over.mk (uOver.left ≫ Y.hom) = Over.mk (snd.left ≫ b) :=
    congrArg Over.mk hbaseChart
  let secU := (F.ι.app (op (Over.mk (uOver.left ≫ Y.hom)))).hom
    ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
      (Over.homMk ((eqToHom eU).left ≫ uOver.left)))
  let secV := (gOver.app (op (Over.mk (snd.left ≫ b))))
    (Over.homMk ((eqToHom eV).left ≫ snd.left))
  have hcompUV : eqToHom eU.symm ≫ eqToHom eUV = eqToHom eV.symm := by
    apply Over.OverMorphism.ext
    simp
  have hinjU : Function.Injective
      (((G ⋙ forget GrpCat).map (eqToHom eU.symm).op).hom) :=
    (ConcreteCategory.bijective_of_isIso
      ((G ⋙ forget GrpCat).map (eqToHom eU.symm).op)).1
  have hsectionHEq : secU ≍ secV := by
    rw [heq_iff_eq_map_eqToHom (G ⋙ forget GrpCat) eUV]
    apply hinjU
    calc
      ((G ⋙ forget GrpCat).map (eqToHom eU.symm).op).hom secU =
          ((G ⋙ forget GrpCat).map (eqToHom eV.symm).op).hom secV := hsectionTransport
      _ = ((G ⋙ forget GrpCat).map (eqToHom eU.symm).op).hom
          (((G ⋙ forget GrpCat).map (eqToHom eUV).op).hom secV) := by
        rw [← Functor.map_comp_apply, ← op_comp, hcompUV]
  have hleftU : (eqToHom eU).left ≫ uOver.left = uOver.left := by simp
  have hleftV : (eqToHom eV).left ≫ snd.left = snd.left := by simp
  have hqNat {Z : Scheme.{u}} (g : Z ⟶ T) :
      (totalPresheaf k (G ⋙ forget GrpCat)).map g.op qR =
        (q ≫ totalTranslation k G r).app (op Z) g := by
    have h := yonedaEquiv_naturality (q ≫ totalTranslation k G r) g
    change (totalPresheaf k (G ⋙ forget GrpCat)).map g.op qR =
      yonedaEquiv (yoneda.map g ≫ q ≫ totalTranslation k G r) at h
    rw [h, yonedaEquiv_apply]
    simp [yoneda_map_app]
  have hmapEta :
      (totalPresheaf k (G ⋙ forget GrpCat)).map snd.left.op qR =
        ⟨snd.left ≫ b,
          ((G ⋙ forget GrpCat).map
            (Over.homMk snd.left : Over.mk (snd.left ≫ b) ⟶ Over.mk b).op).hom x⟩ := rfl
  have hsecVmap : secV =
      ((G ⋙ forget GrpCat).map (eqToHom eV ≫ snd).op).hom x := by
    dsimp [secV, gOver]
    rw [← hmV]
    exact yonedaEquiv_symm_app_apply x (op (Over.mk (snd.left ≫ b)))
      (eqToHom eV ≫ snd)
  have hmapV : eqToHom eV ≫ snd =
      (Over.homMk snd.left : Over.mk (snd.left ≫ b) ⟶ Over.mk b) :=
    Over.OverMorphism.ext hleftV
  have hsecVmap' : secV =
      ((G ⋙ forget GrpCat).map
        (Over.homMk snd.left : Over.mk (snd.left ≫ b) ⟶ Over.mk b).op).hom x := by
    rw [hsecVmap, hmapV]
  have hchartT {Z : Schemeᵒᵖ} (c : Z.unop ⟶ Y.left)
      (w : (totalPresheaf k (G ⋙ forget GrpCat)).obj Z) :
      (totalTranslatedChart k G F Y e r).app Z c = w ↔
        (totalChart k G F Y e).app Z c = (totalTranslation k G r).app Z w := by
    have h := totalTranslation_inv_apply k G r⁻¹ Z w
    rw [inv_inv] at h
    change (totalTranslation k G r⁻¹).app Z ((totalChart k G F Y e).app Z c) = w ↔ _
    constructor
    · rintro rfl
      exact (totalTranslation_inv_apply k G r Z _).symm
    · intro hc
      rw [hc]
      exact h
  have hchart0 :
      (totalChart k G F Y e).app (op P.left) uOver.left =
        (q ≫ totalTranslation k G r).app (op P.left) snd.left := by
    calc
      (totalChart k G F Y e).app (op P.left) uOver.left =
          (totalPresheaf k (G ⋙ forget GrpCat)).map snd.left.op qR := by
        calc
          (totalChart k G F Y e).app (op P.left) uOver.left =
              ⟨snd.left ≫ b,
                ((G ⋙ forget GrpCat).map
                  (Over.homMk snd.left : Over.mk (snd.left ≫ b) ⟶ Over.mk b).op).hom x⟩ := by
            show (⟨uOver.left ≫ Y.hom,
              (F.ι.app (op (Over.mk (uOver.left ≫ Y.hom)))).hom
                ((e.hom.app (op (Over.mk (uOver.left ≫ Y.hom))))
                  (Over.homMk uOver.left))⟩ :
              (totalPresheaf k (G ⋙ forget GrpCat)).obj (op P.left)) = _
            apply Sigma.ext
            · exact hbaseChart
            · simpa [secU, secV, hleftU, hleftV, hsecVmap'] using hsectionHEq
          _ = (totalPresheaf k (G ⋙ forget GrpCat)).map snd.left.op qR := hmapEta.symm
      _ = (q ≫ totalTranslation k G r).app (op P.left) snd.left := hqNat snd.left
  have hchart : (totalTranslatedChart k G F Y e r).app (op P.left) uOver.left =
      q.app (op P.left) snd.left := (hchartT _ _).2 hchart0
  have hcomm : chartMap ≫ totalTranslatedChart k G F Y e r =
      baseMap ≫ q := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp,
      yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    simpa [chartMap, baseMap] using hchart
  refine ⟨P.left, chartMap, snd.left, ?_, hOpenLeft⟩
  let : Mono snd.left := hOpenLeft.mono
  apply IsPullback.of_forall_isPullback_app
  intro Z
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext f
    show (totalTranslatedChart k G F Y e r).app Z ((chartMap.app Z) f) =
      q.app Z ((baseMap.app Z) f)
    exact congrArg (fun η => η.app Z f) hcomm
  · intro f₁ f₂ h
    obtain ⟨hchartEq, hbaseEq⟩ := h
    change f₁ ≫ snd.left = f₂ ≫ snd.left at hbaseEq
    exact (cancel_mono snd.left).1 hbaseEq
  · intro fY fT h
    change (totalTranslatedChart k G F Y e r).app Z
        fY = q.app Z fT at h
    have hsection1 : (totalChart k G F Y e).app Z fY =
        (totalPresheaf k (G ⋙ forget GrpCat)).map fT.op qR :=
      ((hchartT _ _).1 h).trans (hqNat fT).symm
    let mY : Over.mk (fY ≫ Y.hom) ⟶ Y := Over.homMk fY
    let mT : Over.mk (fT ≫ b) ⟶ Over.mk b := Over.homMk fT
    simp only [totalChart] at hsection1
    have hbase : fY ≫ Y.hom = fT ≫ b := by
      have hb := congrArg Sigma.fst hsection1
      change fY ≫ Y.hom = fT ≫ b at hb
      exact hb
    let W : Over (Spec (.of k)) := Over.mk (fY ≫ Y.hom)
    let i : W ⟶ Y := Over.homMk fY
    let eW : W = Over.mk (fT ≫ b) := congrArg Over.mk hbase
    let j0 : Over.mk (fT ≫ b) ⟶ Over.mk b := Over.homMk fT
    let j : W ⟶ Over.mk b := eqToHom eW ≫ j0
    have hcompat :
        (F.ι.app (op W)).hom ((e.hom.app (op W)).hom i) =
          ((G ⋙ forget GrpCat).map j.op).hom x := by
      have hs : (F.ι.app (op W)).hom ((e.hom.app (op W)).hom i) ≍
          ((G ⋙ forget GrpCat).map j0.op).hom x := (Sigma.ext_iff.mp hsection1).2
      have hs' := (heq_iff_eq_map_eqToHom (G ⋙ forget GrpCat) eW _ _).1 hs
      simpa [j, j0, op_comp, Functor.map_comp_apply] using hs'
    obtain ⟨a, haY, haSnd⟩ :=
      totalChart_pullback_lift k G F Y e _ b x P snd fst hPB uOver huYoneda
        W i j hcompat
    refine ⟨a.left, ?_, ?_⟩
    · show a.left ≫ uOver.left = fY
      simpa [i, Over.comp_left] using congrArg Over.Hom.left haY
    · show a.left ≫ snd.left = fT
      calc
        a.left ≫ snd.left = (a ≫ snd).left := rfl
        _ = j.left := congrArg Over.Hom.left haSnd
        _ = fT := by simp [j, j0, Over.comp_left]

private theorem locallySurjective_of_residuePoint_lifts
    {I : Type u} (Y : Scheme.{u}) (T : Schemeᵒᵖ ⥤ Type u)
    (chart : I → (yoneda.obj Y ⟶ T))
    (hchart : ∀ i, IsOpenImmersion.presheaf (chart i))
    (hpoint : ∀ (U : Scheme.{u}) (s : T.obj (op U)) (x : U),
      ∃ i, ∃ t : Spec (U.residueField x) ⟶ Y,
        (chart i).app (op (Spec (U.residueField x))) t =
          T.map (U.fromSpecResidueField x).op s) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc chart) := by
  classical
  constructor
  intro U s
  let q : yoneda.obj U ⟶ T := yonedaEquiv.symm s
  let P (i : I) := (hchart i).rep.pullback q
  let fstNat (i : I) : yoneda.obj (P i) ⟶ yoneda.obj Y :=
    (hchart i).rep.fst q
  let fst (i : I) : P i ⟶ Y := yonedaEquiv (fstNat i)
  let snd (i : I) : P i ⟶ U := (hchart i).rep.snd q
  have hsnd (i : I) : IsOpenImmersion (snd i) :=
    (hchart i).property q (fstNat i) (snd i) ((hchart i).rep.isPullback q)
  let (i : I) : IsOpenImmersion (snd i) := hsnd i
  let O (i : I) : U.Opens := by
    let : IsOpenImmersion (snd i) := hsnd i
    exact (snd i).opensRange
  have hO : TopologicalSpace.IsOpenCover O := by
    apply TopologicalSpace.IsOpenCover.mk
    apply TopologicalSpace.Opens.ext
    ext x
    show x ∈ (⨆ i, O i) ↔ x ∈ (⊤ : U.Opens)
    rw [TopologicalSpace.Opens.mem_iSup]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨i, t, ht⟩ := hpoint U s x
      have heq : yoneda.map t ≫ chart i = yoneda.map (U.fromSpecResidueField x) ≫ q := by
        apply yonedaEquiv.injective
        have hleft : (chart i).app (op (Spec (U.residueField x))) t =
            yonedaEquiv (yoneda.map t ≫ chart i) := by
          rw [← yonedaEquiv_naturality (chart i) t]
          simpa [yonedaEquiv] using
            ConcreteCategory.congr_hom ((chart i).naturality t.op) (𝟙 Y)
        have hright : T.map (U.fromSpecResidueField x).op s =
            yonedaEquiv (yoneda.map (U.fromSpecResidueField x) ≫ q) := by
          calc
            T.map (U.fromSpecResidueField x).op s =
                T.map (U.fromSpecResidueField x).op (yonedaEquiv q) := by simp [q]
            _ = yonedaEquiv (yoneda.map (U.fromSpecResidueField x) ≫ q) :=
              yonedaEquiv_naturality q (U.fromSpecResidueField x)
        exact hleft.symm.trans (ht.trans hright)
      let a := (hchart i).rep.lift (yoneda.map t) (U.fromSpecResidueField x) heq
      have ha : a ≫ snd i = U.fromSpecResidueField x :=
        (hchart i).rep.lift_snd (yoneda.map t) (U.fromSpecResidueField x) heq
      let : IsOpenImmersion (snd i) := hsnd i
      refine ⟨i, ?_⟩
      rw [Scheme.Hom.mem_opensRange]
      have hxrange : x ∈ Set.range (U.fromSpecResidueField x) := by
        rw [Scheme.range_fromSpecResidueField]
        simp
      obtain ⟨p, hp⟩ := hxrange
      refine ⟨a p, ?_⟩
      calc
        snd i (a p) = (a ≫ snd i) p := rfl
        _ = U.fromSpecResidueField x p := by rw [ha]
        _ = x := hp
  let 𝒰 := U.openCoverOfIsOpenCover O hO
  refine Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
  have hbase (i : I) : Presheaf.imageSieve (Sigma.desc chart) s (𝒰.f i) := by
    let e := (snd i).isoOpensRange
    let a : (O i).toScheme ⟶ Y := e.inv ≫ fst i
    have hs : e.inv ≫ snd i = (O i).ι := by simp [e, O]
    have hfst : fstNat i = yoneda.map (fst i) := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map]
    have hfac : yoneda.map a ≫ chart i = yoneda.map (O i).ι ≫ q := by
      have hw := (hchart i).rep.isPullback q
      have haNat : yoneda.map a = yoneda.map e.inv ≫ fstNat i := by
        calc
          yoneda.map a = yoneda.map (e.inv ≫ fst i) := rfl
          _ = yoneda.map e.inv ≫ yoneda.map (fst i) := by rw [Functor.map_comp]
          _ = yoneda.map e.inv ≫ fstNat i := by rw [← hfst]
      calc
        yoneda.map a ≫ chart i =
            (yoneda.map e.inv ≫ fstNat i) ≫ chart i := by rw [haNat]
        _ = yoneda.map e.inv ≫ (yoneda.map (snd i) ≫ q) := by
              rw [Category.assoc, hw.w]
        _ = yoneda.map (O i).ι ≫ q := by
              rw [← Category.assoc, ← Functor.map_comp, hs]
    have hv0 : (chart i).app (op (O i).toScheme) a =
        q.app (op (O i).toScheme) (O i).ι := by
      have h := congrArg (fun η => η.app (op (O i).toScheme) (𝟙 _)) hfac
      simpa [yoneda_map_app] using h
    have hqapp : q.app (op (O i).toScheme) (O i).ι = T.map (O i).ι.op s :=
      yonedaEquiv_symm_app_apply s (op (O i).toScheme) (O i).ι
    have hv := hv0.trans hqapp
    refine ⟨((Sigma.ι (fun j : I => yoneda.obj Y) i).app
      (op (O i).toScheme)) a, ?_⟩
    show ((Sigma.ι (fun j : I => yoneda.obj Y) i ≫ Sigma.desc chart).app
      (op (O i).toScheme)) a = T.map (𝒰.f i).op s
    rw [Sigma.ι_desc]
    exact hv
  intro V f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.ofArrows.exists hf)
  exact (Presheaf.imageSieve (Sigma.desc chart) s).downward_closed (hbase i) g

private lemma totalPresheaf_map_mk (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u)
    {V W : Over (Spec (.of k))} (f : V ⟶ W) (g : G.obj (op W)) :
    (totalPresheaf k G).map f.left.op ⟨W.hom, g⟩ =
      ⟨V.hom, G.map f.op g⟩ := by
  cases V with
  | mk V₀ _ v =>
    cases W with
    | mk W₀ _ w =>
      obtain ⟨a, ha, rfl⟩ := Over.homMk_surjective f
      change V₀ ⟶ W₀ at a
      change a ≫ w = v at ha
      subst v
      rfl

private theorem representableOver_of_totalRepresentable (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u)
    (hG : (totalPresheaf k G).IsRepresentable) : G.IsRepresentable := by
  obtain ⟨T, ⟨rT⟩⟩ := hG.has_representation
  let t := rT.homEquiv (𝟙 T)
  let X : Over (Spec (.of k)) := Over.mk t.1
  have hval (U : Scheme.{u}) (f : U ⟶ T) :
      rT.homEquiv f = (totalPresheaf k G).map f.op t := by
    simpa only [Category.comp_id] using rT.homEquiv_comp f (𝟙 T)
  have hbase (U : Scheme.{u}) (f : U ⟶ T) :
      (rT.homEquiv f).1 = f ≫ t.1 := by
    rw [hval]
    rfl
  have hrelative {V : Over (Spec (.of k))} (f : V ⟶ X) :
      rT.homEquiv f.left =
        (⟨V.hom, G.map f.op t.2⟩ : (totalPresheaf k G).obj (op V.left)) := by
    rw [hval]
    exact totalPresheaf_map_mk k G f t.2
  apply Functor.IsRepresentable.iff_exists_isRepresentedBy.mpr
  refine ⟨X, t.2, ⟨fun {V} => ⟨?_, ?_⟩⟩⟩
  · intro f f' h
    apply Over.OverMorphism.ext
    apply rT.homEquiv.injective
    rw [hrelative, hrelative]
    exact congrArg (fun g : G.obj (op V) =>
      (⟨V.hom, g⟩ : (totalPresheaf k G).obj (op V.left))) h
  · intro g
    let f := rT.homEquiv.symm (⟨V.hom, g⟩ : (totalPresheaf k G).obj (op V.left))
    have hf : rT.homEquiv f = ⟨V.hom, g⟩ := rT.homEquiv.apply_symm_apply _
    have hb : f ≫ t.1 = V.hom := (hbase V.left f).symm.trans (congrArg Sigma.fst hf)
    let m : V ⟶ X := Over.homMk f hb
    refine ⟨m, ?_⟩
    exact eq_of_heq (Sigma.ext_iff.mp ((hrelative m).symm.trans hf)).2

private theorem groupObjectOfRepresentable (S : Scheme.{u})
    (G : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (hG : (G ⋙ forget GrpCat).IsRepresentable) :
    ∃ X : Grp (Over S), Nonempty (yonedaGrp.obj X ≅ G) := by
  obtain ⟨Y, ⟨hY⟩⟩ := hG.has_representation
  let := GrpObj.ofRepresentableBy Y G hY
  exact ⟨⟨Y⟩, ⟨yonedaGrpObjIsoOfRepresentableBy Y G hY⟩⟩

/-- A Zariski sheaf of groups with a representable open subfunctor meeting every
field-valued point after translation by a rational point is a group scheme. -/
@[stacks 0B9Q]
theorem exists_grp_iso_of_representable_openSubfunctor (k : Type u) [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (.of k)))
      (G ⋙ forget GrpCat))
    (F : Subfunctor (G ⋙ forget GrpCat))
    (hF : F.toFunctor.IsRepresentable)
    (hopen : (IsOpenImmersion.over (X := Spec (.of k))).presheaf F.ι)
    (hfield : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (op (fieldExtensionPoint k K))),
      ∃ g' : G.obj (op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (fieldExtensionPoint k K).hom).op).hom g' * g ∈
          F.obj (op (fieldExtensionPoint k K))) :
    ∃ X : Grp (Over (Spec (.of k))), Nonempty (yonedaGrp.obj X ≅ G) := by
  classical
  let B : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  obtain ⟨Y, hY⟩ := hF.has_representation
  let e : yoneda.obj Y ≅ F.toFunctor :=
    Functor.representableByEquiv (Classical.choice hY)
  let I := G.obj (op B)
  let chart (r : I) : yoneda.obj Y.left ⟶ totalPresheaf k (G ⋙ forget GrpCat) :=
    totalTranslatedChart k G F Y e r
  have hchart (r : I) :
      IsOpenImmersion.presheaf (chart r) :=
    totalTranslatedChart_isOpenImmersion k G F Y e r hopen
  have hpoint : ∀ (U : Scheme.{u})
      (s : (totalPresheaf k (G ⋙ forget GrpCat)).obj (op U)) (x : U),
      ∃ r : I, ∃ t : Spec (U.residueField x) ⟶ Y.left,
        (chart r).app (op (Spec (U.residueField x))) t =
          (totalPresheaf k (G ⋙ forget GrpCat)).map
            (U.fromSpecResidueField x).op s := by
    intro U s x
    rcases s with ⟨b, g⟩
    let K : Type u := U.residueField x
    let α : Spec (U.residueField x) ⟶ Spec (.of k) :=
      U.fromSpecResidueField x ≫ b
    let : Algebra k K := RingHom.toAlgebra (Spec.homEquiv α).hom
    let V : Over (Spec (.of k)) := fieldExtensionPoint k K
    have hbase : V.hom = α := by
      apply Spec.homEquiv.injective
      simp [V, fieldExtensionPoint, α, RingHom.algebraMap_toAlgebra]
    let m : V ⟶ Over.mk b := Over.homMk (U.fromSpecResidueField x) (by
        show U.fromSpecResidueField x ≫ b = V.hom
        simpa [α] using hbase.symm)
    let gK := (G.map m.op).hom g
    obtain ⟨r, hr⟩ := hfield K gK
    let z := (G.map (Over.homMk V.hom).op).hom r * gK
    let zF : F.toFunctor.obj (op V) := ⟨z, hr⟩
    let tO : V ⟶ Y := (e.inv.app (op V)) zF
    let t : Spec (U.residueField x) ⟶ Y.left := tO.left
    have htbase : tO.left ≫ Y.hom = V.hom := Over.w tO
    let W : Over (Spec (.of k)) := Over.mk (tO.left ≫ Y.hom)
    have eW : W = V := congrArg Over.mk htbase
    let mEW : W ⟶ V := eqToHom eW
    let tW : W ⟶ Y := mEW ≫ tO
    have hsectionV : (e.hom.app (op V)).hom tO = zF :=
      ConcreteCategory.congr_hom (e.inv_hom_id_app (op V)) zF
    have hsection : (e.hom.app (op W)) tW =
        (F.toFunctor.map (eqToHom eW).op).hom zF := by
      have hn := NatTrans.naturality_apply e.hom mEW.op tO
      simpa [tW, mEW, hsectionV] using hn
    have hinc : ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom z =
        (F.ι.app (op W)).hom ((e.hom.app (op W)).hom tW) := by
      calc
        _ = ((G ⋙ forget GrpCat).map mEW.op).hom
            ((F.ι.app (op V)).hom zF) := rfl
        _ = (F.ι.app (op W)).hom
            ((F.toFunctor.map mEW.op).hom zF) := by
          simpa using (NatTrans.naturality_apply F.ι mEW.op zF).symm
        _ = _ := by rw [hsection.symm]
    have htleft : tW.left = tO.left := by simp [tW, mEW]
    have htOver : (Over.homMk tO.left : W ⟶ Y) = tW := by
      apply Over.OverMorphism.ext
      simp [htleft]
    have hbaseW : tO.left ≫ Y.hom =
        U.fromSpecResidueField x ≫ b :=
      htbase.trans hbase
    let nW : W ⟶ B := Over.homMk W.hom
    let nV : V ⟶ B := Over.homMk V.hom
    let mW : W ⟶ Over.mk b := Over.homMk (U.fromSpecResidueField x) hbaseW.symm
    let mAlpha : Over.mk α ⟶ Over.mk b :=
      Over.homMk (U.fromSpecResidueField x)
    let eBase : W = Over.mk α := congrArg Over.mk hbaseW
    have hncomp : mEW ≫ nV = nW := Over.OverMorphism.ext (Over.w mEW)
    have hmcomp : mEW ≫ m = eqToHom eBase ≫ mAlpha := by
      apply Over.OverMorphism.ext
      simp [mEW, m, mAlpha, Over.comp_left, α]
    refine ⟨r, tO.left, ?_⟩
    have hchartVal : (totalChart k G F Y e).app
        (op (Spec (U.residueField x))) tO.left =
        (⟨W.hom, (F.ι.app (op W)).hom
          ((e.hom.app (op W)).hom tW)⟩ :
          (totalPresheaf k (G ⋙ forget GrpCat)).obj
            (op (Spec (U.residueField x)))) := by
      show (⟨tO.left ≫ Y.hom,
        (F.ι.app (op W)).hom
          ((e.hom.app (op W)).hom (Over.homMk tO.left))⟩ :
          (totalPresheaf k (G ⋙ forget GrpCat)).obj
            (op (Spec (U.residueField x)))) = _
      rw [htOver]
      rfl
    have hlhs :
        (chart r).app (op (Spec (U.residueField x))) tO.left =
          ⟨W.hom, ((G ⋙ forget GrpCat).map nW.op).hom r⁻¹ *
            ((F.ι.app (op W)).hom ((e.hom.app (op W)).hom tW))⟩ := by
      show (totalTranslation k G r⁻¹).app
        (op (Spec (U.residueField x)))
        ((totalChart k G F Y e).app
          (op (Spec (U.residueField x))) tO.left) = _
      dsimp [totalTranslation]
      rw [hchartVal]
      rfl
    have hrhs :
        (totalPresheaf k (G ⋙ forget GrpCat)).map
          (U.fromSpecResidueField x).op ⟨b, g⟩ =
            ⟨α, ((G ⋙ forget GrpCat).map mAlpha.op).hom g⟩ := rfl
    rw [hlhs, hrhs]
    apply Sigma.ext
    · exact hbaseW
    · refine (heq_iff_eq_map_eqToHom (G ⋙ forget GrpCat) eBase _ _).2 ?_
      rw [← hinc]
      show ((G ⋙ forget GrpCat).map nW.op).hom r⁻¹ *
          ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom
            (((G ⋙ forget GrpCat).map nV.op).hom r *
              ((G ⋙ forget GrpCat).map m.op).hom g) =
        ((G ⋙ forget GrpCat).map (eqToHom eBase).op).hom
          (((G ⋙ forget GrpCat).map mAlpha.op).hom g)
      have hmul (a b : (G ⋙ forget GrpCat).obj (op V)) :
          ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom (a * b) =
            ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom a *
              ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom b := by
        show (G.map (eqToHom eW).op).hom (a * b) =
          (G.map (eqToHom eW).op).hom a * (G.map (eqToHom eW).op).hom b
        exact (G.map (eqToHom eW).op).hom.map_mul a b
      rw [hmul]
      have hnr : ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom
          (((G ⋙ forget GrpCat).map nV.op).hom r) =
          ((G ⋙ forget GrpCat).map nW.op).hom r := by
        rw [← Functor.map_comp_apply, ← op_comp, hncomp]
      have hmr : ((G ⋙ forget GrpCat).map (eqToHom eW).op).hom
          (((G ⋙ forget GrpCat).map m.op).hom g) =
          ((G ⋙ forget GrpCat).map (eqToHom eBase).op).hom
            (((G ⋙ forget GrpCat).map mAlpha.op).hom g) := by
        rw [← Functor.map_comp_apply, ← op_comp, hmcomp]
        simp only [← Functor.map_comp_apply, ← op_comp]
      rw [hnr, hmr]
      have hninv : ((G ⋙ forget GrpCat).map nW.op).hom (r⁻¹) =
          (((G ⋙ forget GrpCat).map nW.op).hom r)⁻¹ := by
        show (G.map nW.op).hom (r⁻¹) = ((G.map nW.op).hom r)⁻¹
        exact (G.map nW.op).hom.map_inv r
      rw [hninv]
      group
  let total : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨totalPresheaf k (G ⋙ forget GrpCat),
      (isSheaf_iff_isSheaf_of_type Scheme.zariskiTopology
        (totalPresheaf k (G ⋙ forget GrpCat))).2 (totalPresheaf_isSheaf k
          (G ⋙ forget GrpCat)
          ((isSheaf_iff_isSheaf_of_type
            (Scheme.zariskiTopology.over (Spec (.of k)))
            (G ⋙ forget GrpCat)).1 hG))⟩
  let : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc chart) :=
    locallySurjective_of_residuePoint_lifts Y.left total.1 chart hchart hpoint
  have htotal : total.1.IsRepresentable :=
    Scheme.LocalRepresentability.isRepresentable (F := total) (f := chart) hchart
  have hGrep : (G ⋙ forget GrpCat).IsRepresentable :=
    representableOver_of_totalRepresentable k (G ⋙ forget GrpCat) htotal
  exact groupObjectOfRepresentable (Spec (.of k)) G hGrep

end AlgebraicGeometry

end
