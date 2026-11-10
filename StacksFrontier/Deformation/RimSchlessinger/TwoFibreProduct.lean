module

public import StacksFrontier.CategoryTheory.EqToHomAbsorption
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Condition (RS) for 2-fibre products

Condition (RS) is inherited by a 2-fibre product of categories
cofibered in groupoids.

## Main results

* `satisfiesRS_twoFibreProductOver` proves that condition (RS) is preserved by
  2-fibre products.

## Implementation notes

We use `CategoryTheory.TwoFibreProductOver`, the concrete model of the 2-fibre product of
categories over a base.  The equations saying that the two functors commute with the structure
functors express that they are morphisms over the base; for categories cofibered in groupoids
this is the required notion of 1-morphism.

## References

* [Stacks Project, Tag 06L4](https://stacks.math.columbia.edu/tag/06L4)
-/

@[expose] public section

namespace Deformation

/-! ### Condition (RS) for 2-fibre products -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

/-- A morphism of algebras is surjective if it is after conjugating by `eqToHom`s. -/
private lemma surjective_of_eqToHom_comp_comp_eqToHom
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {A B A' B' : ArtinianLocalAlgCat.{u, v, w} Lambda k} (e : A' = A) (e' : B = B')
    {φ : A ⟶ B} (h : Function.Surjective (eqToHom e ≫ φ ≫ eqToHom e').hom) :
    Function.Surjective φ.hom := by
  subst e e'
  simpa using h

private lemma surjective_component_map
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {H : Type u₁} [Category.{v₁} H]
    {G : Type u₂} [Category.{v₂} G]
    {F : Type u₃} [Category.{v₃} F]
    (pH : H ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (f : H ⥤ F) (g : G ⥤ F)
    {P Q : TwoFibreProductOver pH pG pF f g} (m : P ⟶ Q)
    (h : Function.Surjective m.hbase.hom) :
    Function.Surjective (pH.map m.a).hom := by
  exact surjective_of_eqToHom_comp_comp_eqToHom P.hx.symm Q.hx
    (by simpa only [m.hbase_eq] using h)

private lemma surjective_second_component_map
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {H : Type u₁} [Category.{v₁} H]
    {G : Type u₂} [Category.{v₂} G]
    {F : Type u₃} [Category.{v₃} F]
    (pH : H ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (f : H ⥤ F) (g : G ⥤ F)
    {P Q : TwoFibreProductOver pH pG pF f g} (m : P ⟶ Q)
    (h : Function.Surjective m.hbase.hom) :
    Function.Surjective (pG.map m.b).hom := by
  have : pG.IsHomLift m.hbase m.b := m.hb
  have hm : pG.map m.b = eqToHom P.hy ≫ m.hbase ≫ eqToHom Q.hy.symm := by
    simpa only using IsHomLift.fac' pG m.hbase m.b
  have hbase : m.hbase = eqToHom P.hy.symm ≫ pG.map m.b ≫ eqToHom Q.hy := by
    rw [hm]
    simp [Category.assoc]
  exact surjective_of_eqToHom_comp_comp_eqToHom P.hy.symm Q.hy
    (by simpa only [hbase] using h)

private lemma component_base_naturality
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {H : Type u₁} [Category.{v₁} H]
    {G : Type u₂} [Category.{v₂} G]
    {F : Type u₃} [Category.{v₃} F]
    (pH : H ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (f : H ⥤ F) (g : G ⥤ F)
    {P Q : TwoFibreProductOver pH pG pF f g} (m : P ⟶ Q) :
    pH.map m.a ≫ eqToHom (Q.hx.trans Q.hy.symm) =
      eqToHom (P.hx.trans P.hy.symm) ≫ pG.map m.b := by
  have : pH.IsHomLift m.hbase m.a := m.ha
  have : pG.IsHomLift m.hbase m.b := m.hb
  rw [IsHomLift.fac' pH m.hbase m.a, IsHomLift.fac' pG m.hbase m.b]
  simp [Category.assoc]

private lemma exists_iso_lift_cofibered
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {G : Type u₂} [Category.{v₂} G]
    (p : G ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (hp : IsCofiberedInGroupoids p)
    {x : G} {U : ArtinianLocalAlgCat.{u, v, w} Lambda k}
    (e : p.obj x ≅ U) :
    ∃ (y : G) (_hy : p.obj y = U) (q : x ≅ y), p.IsHomLift e.hom q.hom := by
  obtain ⟨y, q, hq⟩ := hp.exists_lift e.hom.op (Opposite.op x) rfl
  let q' : x ⟶ y.unop := q.unop
  have hy : p.obj y.unop = U := by
    have h := IsHomLift.domain_eq (p := p.op) e.hom.op q
    simpa using congrArg Opposite.unop h
  have hq' : p.IsHomLift e.hom q' := by
    have h := IsHomLift.fac' (p := p.op) e.hom.op q
    apply IsHomLift.of_fac' p e.hom q' rfl hy
    simpa [q', Functor.op_map] using congrArg Quiver.Hom.unop h
  have hqIso : IsIso q := by
    let : p.op.IsHomLift e.hom.op q := hq
    have : Functor.IsStronglyCartesian (p := p.op) e.hom.op q :=
      hp.isStronglyCartesian_homLift e.hom.op q
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p.op) (f := e.hom.op) q
  have : IsIso q' := (isIso_unop_iff q).mpr hqIso
  exact ⟨y.unop, hy, asIso q', hq'⟩

/-- Replacing the cone point of a limit pullback cone by an isomorphic object, along an
isomorphism, gives a limit pullback cone. -/
private def isLimit_mk_inv_comp {C : Type u₁} [Category.{v₁} C] {X₁ X₂ X : C}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {c : PullbackCone f₁ f₂} (hc : IsLimit c) {Y : C}
    (q : c.pt ≅ Y) :
    IsLimit (PullbackCone.mk (f := f₁) (g := f₂) (q.inv ≫ c.fst) (q.inv ≫ c.snd)
      (by simp [c.condition])) :=
  IsLimit.ofIsoLimit hc <| PullbackCone.ext q
    (by change c.fst = q.hom ≫ q.inv ≫ c.fst; simp)
    (by change c.snd = q.hom ≫ q.inv ≫ c.snd; simp)

/-- The image under a functor of the cone of `isLimit_mk_inv_comp` is a limit cone as soon as
the image of the original cone is. -/
private def isLimit_map_mk_inv_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D)
    {X₁ X₂ X : C} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {c : PullbackCone f₁ f₂}
    (hc : IsLimit (c.map F)) {Y : C} (q : c.pt ≅ Y) :
    IsLimit ((PullbackCone.mk (f := f₁) (g := f₂) (q.inv ≫ c.fst) (q.inv ≫ c.snd)
      (by simp [c.condition])).map F) :=
  IsLimit.ofIsoLimit hc <| PullbackCone.ext (F.mapIso q)
    (by change F.map c.fst = F.map q.hom ≫ F.map (q.inv ≫ c.fst); simp)
    (by change F.map c.snd = F.map q.hom ≫ F.map (q.inv ≫ c.snd); simp)

private lemma exists_rebased_pullback
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {G : Type u₂} [Category.{v₂} G]
    (p : G ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (hp : IsCofiberedInGroupoids p)
    {x₁ x₂ x : G} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hcb : IsLimit (c.map p))
    {U : ArtinianLocalAlgCat.{u, v, w} Lambda k}
    (e : p.obj c.pt ≅ U) :
    ∃ d : PullbackCone f₁ f₂,
      p.obj d.pt = U ∧ Nonempty (IsLimit d) ∧ Nonempty (IsLimit (d.map p)) := by
  obtain ⟨y, hy, q, _⟩ := exists_iso_lift_cofibered p hp e
  exact ⟨_, hy, ⟨isLimit_mk_inv_comp hc q⟩, ⟨isLimit_map_mk_inv_comp p hcb q⟩⟩

private lemma base_eq_of_comparison
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {H : Type u₁} [Category.{v₁} H]
    {G : Type u₂} [Category.{v₂} G]
    {F : Type u₃} [Category.{v₃} F]
    (pF : F ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (f : H ⥤ F) (g : G ⥤ F)
    {P Q : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (hw : f.map a ≫ Q.iso.hom = P.iso.hom ≫ g.map b) :
    eqToHom P.hy.symm ≫ (g ⋙ pF).map b ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ (f ⋙ pF).map a ≫ eqToHom Q.hx := by
  have : pF.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have : pF.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
  have hP : pF.map P.iso.hom = eqToHom P.hx ≫ eqToHom P.hy.symm := by
    simpa only [Category.comp_id, Category.id_comp] using
      IsHomLift.fac' pF (𝟙 P.base) P.iso.hom
  have hQ : pF.map Q.iso.hom = eqToHom Q.hx ≫ eqToHom Q.hy.symm := by
    simpa only [Category.comp_id, Category.id_comp] using
      IsHomLift.fac' pF (𝟙 Q.base) Q.iso.hom
  have h := congrArg (fun z ↦ pF.map z) hw
  simp only [pF.map_comp, hP, hQ] at h
  have h' := congrArg (fun z ↦ eqToHom P.hx.symm ≫ z ≫ eqToHom Q.hy) h
  simpa [Category.assoc] using h'.symm

private lemma pullbackPointIsoOfIsoCospans
    {C : Type*} [Category C]
    {X₁ X₂ X Z₁ Z₂ Z : C}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    {g₁ : Z₁ ⟶ Z} {g₂ : Z₂ ⟶ Z}
    (i₁ : X₁ ≅ Z₁) (i₂ : X₂ ≅ Z₂) (i : X ≅ Z)
    (h₁ : f₁ ≫ i.hom = i₁.hom ≫ g₁)
    (h₂ : f₂ ≫ i.hom = i₂.hom ≫ g₂)
    (c₁ : PullbackCone f₁ f₂) (hc₁ : IsLimit c₁)
    (c₂ : PullbackCone g₁ g₂) (hc₂ : IsLimit c₂) :
    ∃ e : c₁.pt ≅ c₂.pt,
      e.hom ≫ c₂.fst = c₁.fst ≫ i₁.hom ∧
      e.hom ≫ c₂.snd = c₁.snd ≫ i₂.hom := by
  have h₁' : i₁.inv ≫ f₁ = g₁ ≫ i.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₂' : i₂.inv ≫ f₂ = g₂ ≫ i.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let s₂ : PullbackCone g₁ g₂ := PullbackCone.mk (c₁.fst ≫ i₁.hom) (c₁.snd ≫ i₂.hom) (by
    calc
      (c₁.fst ≫ i₁.hom) ≫ g₁ = c₁.fst ≫ (i₁.hom ≫ g₁) := by simp [Category.assoc]
      _ = c₁.fst ≫ f₁ ≫ i.hom := by rw [← h₁]
      _ = c₁.snd ≫ f₂ ≫ i.hom := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ i.hom) c₁.condition
      _ = (c₁.snd ≫ i₂.hom) ≫ g₂ := by simp only [Category.assoc, ← h₂])
  let s₁ : PullbackCone f₁ f₂ := PullbackCone.mk (c₂.fst ≫ i₁.inv) (c₂.snd ≫ i₂.inv) (by
    calc
      (c₂.fst ≫ i₁.inv) ≫ f₁ = c₂.fst ≫ (i₁.inv ≫ f₁) := by simp [Category.assoc]
      _ = c₂.fst ≫ g₁ ≫ i.inv := by rw [h₁']
      _ = c₂.snd ≫ g₂ ≫ i.inv := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ i.inv) c₂.condition
      _ = (c₂.snd ≫ i₂.inv) ≫ f₂ := by simp only [Category.assoc, h₂'])
  let eHom : c₁.pt ⟶ c₂.pt := hc₂.lift s₂
  let eInv : c₂.pt ⟶ c₁.pt := hc₁.lift s₁
  have heHom₁ : eHom ≫ c₂.fst = c₁.fst ≫ i₁.hom := hc₂.fac s₂ WalkingCospan.left
  have heHom₂ : eHom ≫ c₂.snd = c₁.snd ≫ i₂.hom := hc₂.fac s₂ WalkingCospan.right
  have heInv₁ : eInv ≫ c₁.fst = c₂.fst ≫ i₁.inv := hc₁.fac s₁ WalkingCospan.left
  have heInv₂ : eInv ≫ c₁.snd = c₂.snd ≫ i₂.inv := hc₁.fac s₁ WalkingCospan.right
  have hcomp₁ : eHom ≫ eInv = 𝟙 c₁.pt := by
    apply PullbackCone.IsLimit.hom_ext hc₁
    · simp only [Category.assoc, heInv₁, Category.id_comp]
      rw [← Category.assoc, heHom₁]
      simp
    · simp only [Category.assoc, heInv₂, Category.id_comp]
      rw [← Category.assoc, heHom₂]
      simp
  have hcomp₂ : eInv ≫ eHom = 𝟙 c₂.pt := by
    apply PullbackCone.IsLimit.hom_ext hc₂
    · simp only [Category.assoc, heHom₁, Category.id_comp]
      rw [← Category.assoc, heInv₁]
      simp
    · simp only [Category.assoc, heHom₂, Category.id_comp]
      rw [← Category.assoc, heInv₂]
      simp
  exact ⟨⟨eHom, eInv, hcomp₁, hcomp₂⟩, heHom₁, heHom₂⟩



/-- In a category cofibered in groupoids, a morphism `a` over `α` and a morphism `b` over
`α ≫ β` factor uniquely through `a` as a morphism over `β`. -/
private lemma exists_unique_isHomLift_comp_eq
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (p : D ⥤ C)
    (hp : IsCofiberedInGroupoids p) {x y z : D} {U V W : C}
    (hx : p.obj x = U) (hy : p.obj y = V) (hz : p.obj z = W)
    {α : U ⟶ V} {β : V ⟶ W} {γ : U ⟶ W} (h : α ≫ β = γ) (a : x ⟶ y) (b : x ⟶ z)
    [p.IsHomLift α a] [p.IsHomLift γ b] :
    ∃ c : y ⟶ z, p.IsHomLift β c ∧ a ≫ c = b ∧
      ∀ c' : y ⟶ z, p.IsHomLift β c' → a ≫ c' = b → c' = c := by
  subst hx hy hz h
  have ha : p.map a = α := by simpa using IsHomLift.fac' p α a
  have hb : p.map b = α ≫ β := by simpa using IsHomLift.fac' p (α ≫ β) b
  obtain ⟨c, ⟨hc, hac⟩, hu⟩ := hp.unique_lift a.op b.op β.op
    (Quiver.Hom.unop_inj (by simp [ha, hb]))
  refine ⟨c.unop, ?_, congrArg Quiver.Hom.unop hac, fun c' hc' hac' => ?_⟩
  · rw [← show p.map c.unop = β from congrArg Quiver.Hom.unop hc]
    infer_instance
  · have hc'map : p.map c' = β := by simpa using IsHomLift.fac' p β c'
    simpa using congrArg Quiver.Hom.unop
      (hu c'.op ⟨congrArg Quiver.Hom.op hc'map, congrArg Quiver.Hom.op hac'⟩)

/-- If `a` lies over `α` and `F` is a morphism over the base, then `F a` lies over `α` in the
opposite categories. -/
private lemma isHomLift_op_map
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (p : D ⥤ C) (q : E ⥤ C) (F : D ⥤ E) (hF : F ⋙ q = p)
    {U V : C} (α : U ⟶ V) {x y : D} (a : x ⟶ y) [p.IsHomLift α a] :
    q.op.IsHomLift α.op (F.map a).op :=
  have := Functor.isHomLift_map_of_comp_eq hF α a
  isHomLift_op q α (F.map a)

/-- A 2-fibre product of categories satisfying condition (RS) again satisfies condition
(RS). -/
@[stacks 06L4]
theorem satisfiesRS_twoFibreProductOver
    {Lambda : Type u} {k : Type w} [CommRing Lambda] [Field k] [Algebra Lambda k]
    {H : Type u₁} [Category.{v₁} H]
    {G : Type u₂} [Category.{v₂} G]
    {F : Type u₃} [Category.{v₃} F]
    (pH : H ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, v, w} Lambda k)
    (f : H ⥤ F) (g : G ⥤ F)
    (hf : f ⋙ pF = pH) (hg : g ⋙ pF = pG)
    (hH : SatisfiesRS pH)
    (hG : SatisfiesRS pG)
    (hF : SatisfiesRS pF) :
    SatisfiesRS
      (TwoFibreProductOver.structureFunctor pH pG pF f g) :=
  by
    subst pH
    subst pG
    let pH := f ⋙ pF
    let pG := g ⋙ pF
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro V U α X hX
        rcases X with ⟨P⟩
        change Opposite.op P.base = U at hX
        subst U
        obtain ⟨X, a, ha⟩ := hH.1.exists_lift α (Opposite.op P.x) (by
          simpa using congrArg Opposite.op P.hx)
        obtain ⟨Y, b, hb⟩ := hG.1.exists_lift α (Opposite.op P.y) (by
          simpa using congrArg Opposite.op P.hy)
        have ha' : pH.IsHomLift α.unop a.unop := isHomLift_unop pH α a (inst := ha)
        have hb' : pG.IsHomLift α.unop b.unop := isHomLift_unop pG α b (inst := hb)
        have hX : pH.obj X.unop = V.unop := congrArg Opposite.unop (IsHomLift.domain_eq pH.op α a)
        have hY : pG.obj Y.unop = V.unop := congrArg Opposite.unop (IsHomLift.domain_eq pG.op α b)
        have hFa : pF.op.IsHomLift α (f.map a.unop).op := by
          let := ha'
          exact isHomLift_op_map pH pF f rfl α.unop a.unop
        have hGb : pF.op.IsHomLift α (g.map b.unop).op := by
          let := hb'
          exact isHomLift_op_map pG pF g rfl α.unop b.unop
        have hPi : pF.op.IsHomLift (𝟙 (Opposite.op P.base)) P.iso.hom.op := by
          let := P.vertical
          simpa only [op_id] using isHomLift_op pF (𝟙 P.base) P.iso.hom
        have hComp : pF.op.IsHomLift α (P.iso.hom ≫ g.map b.unop).op := by
          let := hGb
          let := hPi
          simpa only [op_comp, Category.comp_id] using
            (IsHomLift.comp pF.op α (𝟙 (Opposite.op P.base))
              (g.map b.unop).op P.iso.hom.op)
        let := hFa
        let := hComp
        have hscFa := hF.1.isStronglyCartesian_homLift α (f.map a.unop).op
        have hscComp := hF.1.isStronglyCartesian_homLift α (P.iso.hom ≫ g.map b.unop).op
        let cOp : Opposite.op (g.obj Y.unop) ≅ Opposite.op (f.obj X.unop) :=
          Functor.IsStronglyCartesian.domainIsoOfBaseIso pF.op
            (g := Iso.refl V) (show α = (Iso.refl V).hom ≫ α by simp) (f.map a.unop).op
            (P.iso.hom ≫ g.map b.unop).op
        have hcVertOp : pF.op.IsHomLift (𝟙 V) cOp.hom := by
          change pF.op.IsHomLift (Iso.refl V).hom cOp.hom
          exact inferInstance
        have hcVert : pF.IsHomLift (𝟙 V.unop) cOp.unop.hom := by
          change pF.IsHomLift (𝟙 V.unop) cOp.hom.unop
          simpa only [unop_id] using isHomLift_unop pF (𝟙 V) cOp.hom (inst := hcVertOp)
        have hcSquare : f.map a.unop ≫ cOp.unop.hom =
            P.iso.hom ≫ g.map b.unop := by
          apply Quiver.Hom.op_inj
          change cOp.hom ≫ (f.map a.unop).op = (P.iso.hom ≫ g.map b.unop).op
          exact Functor.IsStronglyCartesian.fac pF.op α (f.map a.unop).op
            (show α = (Iso.refl V).hom ≫ α by simp)
            (P.iso.hom ≫ g.map b.unop).op
        let Q : TwoFibreProductOver pH pG pF f g :=
          { base := V.unop, x := X.unop, y := Y.unop, hx := hX, hy := hY,
            iso := cOp.unop, vertical := hcVert }
        let m : P ⟶ Q :=
          { hbase := α.unop, a := a.unop, b := b.unop,
            ha := ha', hb := hb', w := hcSquare }
        have hm : (TwoFibreProductOver.structureFunctor pH pG pF f g).op.IsHomLift α m.op := by
          have : (TwoFibreProductOver.structureFunctor pH pG pF f g).IsHomLift α.unop m :=
            IsHomLift.map (p := TwoFibreProductOver.structureFunctor pH pG pF f g) m
          exact isHomLift_op _ α.unop m
        exact ⟨Opposite.op Q, m.op, hm⟩
      · intro X Y Z φ ψ β hβ
        rcases X with ⟨P⟩; rcases Y with ⟨Q⟩; rcases Z with ⟨R⟩
        change β ≫ φ.unop.hbase.op = ψ.unop.hbase.op at hβ
        have hβ' : φ.unop.hbase ≫ β.unop = ψ.unop.hbase := congrArg Quiver.Hom.unop hβ
        have := φ.unop.ha
        have := ψ.unop.ha
        have := φ.unop.hb
        have := ψ.unop.hb
        obtain ⟨a', haLift, haFac', haUniq⟩ :=
          exists_unique_isHomLift_comp_eq pH hH.1 P.hx Q.hx R.hx hβ' φ.unop.a ψ.unop.a
        obtain ⟨b', hbLift, hbFac', hbUniq⟩ :=
          exists_unique_isHomLift_comp_eq pG hG.1 P.hy Q.hy R.hy hβ' φ.unop.b ψ.unop.b
        change pH.IsHomLift β.unop a' at haLift
        change pG.IsHomLift β.unop b' at hbLift
        have hfa : pF.IsHomLift β.unop (f.map a') :=
          Functor.isHomLift_map_of_comp_eq (p := pH) (q := pF) (G := f) rfl β.unop a'
        have hgb : pF.IsHomLift β.unop (g.map b') :=
          Functor.isHomLift_map_of_comp_eq (p := pG) (q := pF) (G := g) rfl β.unop b'
        have hA : pF.IsHomLift β.unop (f.map a' ≫ R.iso.hom) := by
          rw [← Category.comp_id β.unop]
          exact @IsHomLift.comp _ _ _ _ pF _ _ _ _ _ _ β.unop (𝟙 R.base)
            (f.map a') R.iso.hom hfa R.vertical
        have hB : pF.IsHomLift β.unop (Q.iso.hom ≫ g.map b') := by
          rw [← Category.id_comp β.unop]
          exact @IsHomLift.comp _ _ _ _ pF _ _ _ _ _ _ (𝟙 Q.base) β.unop
            Q.iso.hom (g.map b') Q.vertical hgb
        have hpre : f.map φ.unop.a ≫ (f.map a' ≫ R.iso.hom) =
            f.map φ.unop.a ≫ (Q.iso.hom ≫ g.map b') := by
          calc
            _ = (f.map φ.unop.a ≫ f.map a') ≫ R.iso.hom := by
              rw [Category.assoc]
            _ = f.map (φ.unop.a ≫ a') ≫ R.iso.hom := by
              rw [Functor.map_comp]
            _ = f.map ψ.unop.a ≫ R.iso.hom := by rw [haFac']
            _ = P.iso.hom ≫ g.map ψ.unop.b := ψ.unop.w
            _ = P.iso.hom ≫ g.map (φ.unop.b ≫ b') := by rw [hbFac']
            _ = P.iso.hom ≫ (g.map φ.unop.b ≫ g.map b') := by
              rw [Functor.map_comp]
            _ = (P.iso.hom ≫ g.map φ.unop.b) ≫ g.map b' := by
              rw [Category.assoc]
            _ = (f.map φ.unop.a ≫ Q.iso.hom) ≫ g.map b' := by
              rw [φ.unop.w]
            _ = _ := by rw [Category.assoc]
        have hφaOp : pF.op.IsHomLift φ.unop.hbase.op (f.map φ.unop.a).op :=
          isHomLift_op_map pH pF f rfl φ.unop.hbase φ.unop.a
        have hAOp : pF.op.IsHomLift β (f.map a' ≫ R.iso.hom).op := by
          let := hA
          simpa only [Quiver.Hom.op_unop] using
            isHomLift_op pF β.unop (f.map a' ≫ R.iso.hom)
        have hBOp : pF.op.IsHomLift β (Q.iso.hom ≫ g.map b').op := by
          let := hB
          simpa only [Quiver.Hom.op_unop] using
            isHomLift_op pF β.unop (Q.iso.hom ≫ g.map b')
        have hpreOp : (f.map a' ≫ R.iso.hom).op ≫ (f.map φ.unop.a).op =
            (Q.iso.hom ≫ g.map b').op ≫ (f.map φ.unop.a).op := by
          simpa only [op_comp] using congrArg Quiver.Hom.op hpre
        have hcomparison : f.map a' ≫ R.iso.hom =
            Q.iso.hom ≫ g.map b' := by
          apply Quiver.Hom.op_inj
          let := hφaOp
          let := hAOp
          let := hBOp
          have hsc := hF.1.isStronglyCartesian_homLift
            φ.unop.hbase.op (f.map φ.unop.a).op
          exact @Functor.IsStronglyCartesian.ext _ _ _ _ pF.op _ _ _ _
            φ.unop.hbase.op (f.map φ.unop.a).op hsc _ _ β _ _ hAOp hBOp hpreOp
        let m : Q ⟶ R :=
          { hbase := β.unop, a := a', b := b',
            ha := haLift, hb := hbLift, w := hcomparison }
        refine ⟨m.op, ⟨?_, ?_⟩, ?_⟩
        · change β.unop.op = β
          exact Quiver.Hom.op_unop β
        · apply Quiver.Hom.unop_inj
          change φ.unop ≫ m = ψ.unop
          apply TwoFibreProductOver.Hom.ext'
          · exact haFac'
          · exact hbFac'
        · intro χ hχ
          rcases hχ with ⟨hχmap, hχfac⟩
          have hbaseχ : χ.unop.hbase = β.unop := congrArg Quiver.Hom.unop hχmap
          have hfacχ : φ.unop ≫ χ.unop = ψ.unop := congrArg Quiver.Hom.unop hχfac
          have hχa : χ.unop.a = a' :=
            haUniq _ (hbaseχ ▸ χ.unop.ha) (congrArg TwoFibreProductOver.Hom.a hfacχ)
          have hχb : χ.unop.b = b' :=
            hbUniq _ (hbaseχ ▸ χ.unop.hb) (congrArg TwoFibreProductOver.Hom.b hfacχ)
          apply Quiver.Hom.unop_inj
          change χ.unop = m
          exact TwoFibreProductOver.Hom.ext' hχa hχb
    · intro P₁ P₂ P m₁ m₂ hsurj
      have hsurjH : Function.Surjective (pH.map m₂.a).hom :=
        surjective_component_map pH pG pF f g m₂ hsurj
      have hsurjG : Function.Surjective (pG.map m₂.b).hom :=
        surjective_second_component_map pH pG pF f g m₂ hsurj
      obtain ⟨cH, ⟨hcH⟩, ⟨hcBH⟩⟩ := hH.2 m₁.a m₂.a hsurjH
      obtain ⟨cG, ⟨hcG⟩, ⟨hcBG⟩⟩ := hG.2 m₁.b m₂.b hsurjG
      let i₁ : pH.obj P₁.x ≅ pG.obj P₁.y :=
        eqToIso (P₁.hx.trans P₁.hy.symm)
      let i₂ : pH.obj P₂.x ≅ pG.obj P₂.y :=
        eqToIso (P₂.hx.trans P₂.hy.symm)
      let i : pH.obj P.x ≅ pG.obj P.y :=
        eqToIso (P.hx.trans P.hy.symm)
      have hmap₁ : pH.map m₁.a ≫ i.hom = i₁.hom ≫ pG.map m₁.b :=
        component_base_naturality pH pG pF f g m₁
      have hmap₂ : pH.map m₂.a ≫ i.hom = i₂.hom ≫ pG.map m₂.b :=
        component_base_naturality pH pG pF f g m₂
      obtain ⟨e, he₁, he₂⟩ :=
        pullbackPointIsoOfIsoCospans i₁ i₂ i hmap₁ hmap₂
          (cH.map pH) hcBH (cG.map pG) hcBG
      obtain ⟨dG, hdG, ⟨hlimG⟩, ⟨hbaseG⟩⟩ :=
        exists_rebased_pullback pG hG.1 m₁.b m₂.b cG hcG hcBG e.symm
      let hcFH := (isLimit_of_map_isLimit
        (p := pF) hF (f.map m₁.a) (f.map m₂.a) (cH.map f) hsurjH ⟨hcBH⟩).some
      let hcFG := (isLimit_of_map_isLimit
        (p := pF) hF (g.map m₁.b) (g.map m₂.b) (dG.map g) hsurjG ⟨hbaseG⟩).some
      obtain ⟨compIso, hcomp₁, hcomp₂⟩ :=
        pullbackPointIsoOfIsoCospans P₁.iso P₂.iso P.iso m₁.w m₂.w
          (cH.map f) hcFH (dG.map g) hcFG
      let baseIso : pG.obj dG.pt ≅ pH.obj cH.pt :=
        (pF.mapIso compIso).symm
      obtain ⟨y, hy, q, hq⟩ := exists_iso_lift_cofibered pG hG.1 baseIso
      let dG' : PullbackCone m₁.b m₂.b :=
        PullbackCone.mk (q.inv ≫ dG.fst) (q.inv ≫ dG.snd) (by
          simp [Category.assoc, dG.condition])
      have hdG' : IsLimit dG' := isLimit_mk_inv_comp hlimG q
      let compIso' : f.obj cH.pt ≅ g.obj dG'.pt :=
        compIso ≪≫ g.mapIso q
      have hqmap : pG.map q.hom = baseIso.hom ≫ eqToHom hy.symm := by
        have : pG.IsHomLift baseIso.hom q.hom := hq
        simpa using IsHomLift.fac' pG baseIso.hom q.hom
      have hmapcomp : pF.map (compIso.hom ≫ g.map q.hom) =
          pF.map compIso.hom ≫ pG.map q.hom := pF.map_comp _ _
      have hvert : pF.IsHomLift (𝟙 (pH.obj cH.pt)) compIso'.hom := by
        apply IsHomLift.of_fac' pF (𝟙 _) compIso'.hom rfl hy
        change pF.map (compIso.hom ≫ g.map q.hom) = _
        rw [hmapcomp, hqmap]
        change pF.map compIso.hom ≫ pF.map compIso.inv ≫ eqToHom hy.symm = _
        simp
      have hw : ∀ {X₁ : H} {Y₁ : G} (s : cH.pt ⟶ X₁) (t : dG.pt ⟶ Y₁) (ι : f.obj X₁ ≅ g.obj Y₁),
          compIso.hom ≫ g.map t = f.map s ≫ ι.hom →
            f.map s ≫ ι.hom = compIso'.hom ≫ g.map (q.inv ≫ t) := by
        intro X₁ Y₁ s t ι h
        have h' : g.map t = g.map q.hom ≫ g.map (q.inv ≫ t) := by
          rw [← g.map_comp, q.hom_inv_id_assoc]
        exact (h.symm.trans (congrArg (compIso.hom ≫ ·) h')).trans (Category.assoc _ _ _).symm
      have hw₁ : f.map cH.fst ≫ P₁.iso.hom = compIso'.hom ≫ g.map dG'.fst :=
        hw cH.fst dG.fst P₁.iso hcomp₁
      have hw₂ : f.map cH.snd ≫ P₂.iso.hom = compIso'.hom ≫ g.map dG'.snd :=
        hw cH.snd dG.snd P₂.iso hcomp₂
      let T : TwoFibreProductOver pH pG pF f g :=
        { base := pH.obj cH.pt
          x := cH.pt
          y := dG'.pt
          hx := rfl
          hy := hy
          iso := compIso'
          vertical := hvert }
      have hbase₁ := base_eq_of_comparison (P := T) (Q := P₁)
        pF f g cH.fst dG'.fst hw₁
      have hbase₂ := base_eq_of_comparison (P := T) (Q := P₂)
        pF f g cH.snd dG'.snd hw₂
      let l₁ : T ⟶ P₁ :=
        TwoFibreProductOver.Hom.mk' (P := T) (Q := P₁) cH.fst dG'.fst hbase₁ hw₁
      let l₂ : T ⟶ P₂ :=
        TwoFibreProductOver.Hom.mk' (P := T) (Q := P₂) cH.snd dG'.snd hbase₂ hw₂
      have hcondition : l₁ ≫ m₁ = l₂ ≫ m₂ := by
        apply TwoFibreProductOver.Hom.ext'
        · change cH.fst ≫ m₁.a = cH.snd ≫ m₂.a
          exact cH.condition
        · change dG'.fst ≫ m₁.b = dG'.snd ≫ m₂.b
          exact dG'.condition
      let c : PullbackCone m₁ m₂ := PullbackCone.mk l₁ l₂ hcondition
      have hcFG' : IsLimit (dG'.map g) := isLimit_map_mk_inv_comp g hcFG q
      let sH (s : PullbackCone m₁ m₂) : PullbackCone m₁.a m₂.a :=
        PullbackCone.mk s.fst.a s.snd.a (by
          have h := congrArg TwoFibreProductOver.Hom.a s.condition
          exact h)
      let sG (s : PullbackCone m₁ m₂) : PullbackCone m₁.b m₂.b :=
        PullbackCone.mk s.fst.b s.snd.b (by
          have h := congrArg TwoFibreProductOver.Hom.b s.condition
          exact h)
      let liftS (s : PullbackCone m₁ m₂) : s.pt ⟶ T := by
        let a : s.pt.x ⟶ cH.pt := hcH.lift (sH s)
        let b : s.pt.y ⟶ dG'.pt := hdG'.lift (sG s)
        have ha₁ : a ≫ cH.fst = s.fst.a := hcH.fac (sH s) WalkingCospan.left
        have ha₂ : a ≫ cH.snd = s.snd.a := hcH.fac (sH s) WalkingCospan.right
        have hb₁ : b ≫ dG'.fst = s.fst.b := hdG'.fac (sG s) WalkingCospan.left
        have hb₂ : b ≫ dG'.snd = s.snd.b := hdG'.fac (sG s) WalkingCospan.right
        have hwc : ∀ {X₁ : H} {Y₁ : G} (cs : cH.pt ⟶ X₁) (ct : dG'.pt ⟶ Y₁)
            (ι : f.obj X₁ ≅ g.obj Y₁) (sa : s.pt.x ⟶ X₁) (sb : s.pt.y ⟶ Y₁),
            f.map sa ≫ ι.hom = s.pt.iso.hom ≫ g.map sb →
            f.map cs ≫ ι.hom = compIso'.hom ≫ g.map ct → a ≫ cs = sa → b ≫ ct = sb →
            (f.map a ≫ compIso'.hom) ≫ g.map ct = (s.pt.iso.hom ≫ g.map b) ≫ g.map ct := by
          rintro X₁ Y₁ cs ct ι _ _ hs hc rfl rfl
          rw [Category.assoc, ← hc, ← Category.assoc, ← f.map_comp, hs, g.map_comp,
            Category.assoc]
        have hw : f.map a ≫ compIso'.hom = s.pt.iso.hom ≫ g.map b := by
          apply PullbackCone.IsLimit.hom_ext hcFG'
          · exact hwc _ _ P₁.iso _ _ s.fst.w hw₁ ha₁ hb₁
          · exact hwc _ _ P₂.iso _ _ s.snd.w hw₂ ha₂ hb₂
        exact TwoFibreProductOver.Hom.mk' (P := s.pt) (Q := T) a b
          (base_eq_of_comparison (P := s.pt) (Q := T) pF f g a b hw) hw
      have lift_fac_left (s : PullbackCone m₁ m₂) : liftS s ≫ l₁ = s.fst :=
        TwoFibreProductOver.Hom.ext' (hcH.fac (sH s) WalkingCospan.left)
          (hdG'.fac (sG s) WalkingCospan.left)
      have lift_fac_right (s : PullbackCone m₁ m₂) : liftS s ≫ l₂ = s.snd :=
        TwoFibreProductOver.Hom.ext' (hcH.fac (sH s) WalkingCospan.right)
          (hdG'.fac (sG s) WalkingCospan.right)
      have lift_unique (s : PullbackCone m₁ m₂) (m : s.pt ⟶ T)
          (h₁ : m ≫ l₁ = s.fst) (h₂ : m ≫ l₂ = s.snd) : m = liftS s := by
        have hl₁ := lift_fac_left s
        have hl₂ := lift_fac_right s
        apply TwoFibreProductOver.Hom.ext'
        · apply PullbackCone.IsLimit.hom_ext hcH
          · exact (congrArg TwoFibreProductOver.Hom.a h₁).trans
              (congrArg TwoFibreProductOver.Hom.a hl₁).symm
          · exact (congrArg TwoFibreProductOver.Hom.a h₂).trans
              (congrArg TwoFibreProductOver.Hom.a hl₂).symm
        · apply PullbackCone.IsLimit.hom_ext hdG'
          · exact (congrArg TwoFibreProductOver.Hom.b h₁).trans
              (congrArg TwoFibreProductOver.Hom.b hl₁).symm
          · exact (congrArg TwoFibreProductOver.Hom.b h₂).trans
              (congrArg TwoFibreProductOver.Hom.b hl₂).symm
      have hc : IsLimit c :=
        PullbackCone.IsLimit.mk hcondition liftS lift_fac_left lift_fac_right lift_unique
      have hmbase {P' : TwoFibreProductOver pH pG pF f g} (m : P' ⟶ P) :
          pH.map m.a = eqToHom P'.hx ≫ m.hbase ≫ eqToHom P.hx.symm := by
        have : pH.IsHomLift m.hbase m.a := m.ha
        simpa using IsHomLift.fac' pH m.hbase m.a
      have hl₁base : l₁.hbase = pH.map cH.fst ≫ eqToHom P₁.hx := by
        simp [l₁, T]
      have hl₂base : l₂.hbase = pH.map cH.snd ≫ eqToHom P₂.hx := by
        simp [l₂, T]
      let pT := TwoFibreProductOver.structureFunctor pH pG pF f g
      have hcbase : IsLimit (c.map pT) := by
        let baseCone : PullbackCone m₁.hbase m₂.hbase := c.map pT
        change IsLimit baseCone
        let sHbase (s : PullbackCone m₁.hbase m₂.hbase) :
            PullbackCone (pH.map m₁.a) (pH.map m₂.a) :=
          PullbackCone.mk (s.fst ≫ eqToHom P₁.hx.symm)
            (s.snd ≫ eqToHom P₂.hx.symm) (by
              rw [hmbase m₁, hmbase m₂]
              simpa [Category.assoc] using
                congrArg (fun z ↦ z ≫ eqToHom P.hx.symm) s.condition)
        let liftB (s : PullbackCone m₁.hbase m₂.hbase) : s.pt ⟶ baseCone.pt :=
          hcBH.lift (sHbase s)
        have fac₁ (s : PullbackCone m₁.hbase m₂.hbase) :
            liftB s ≫ baseCone.fst = s.fst := by
          change hcBH.lift (sHbase s) ≫ l₁.hbase = s.fst
          rw [hl₁base]
          exact (Category.assoc _ _ _).symm.trans
            ((comp_eqToHom_iff _ _ _).mpr (hcBH.fac (sHbase s) WalkingCospan.left))
        have fac₂ (s : PullbackCone m₁.hbase m₂.hbase) :
            liftB s ≫ baseCone.snd = s.snd := by
          change hcBH.lift (sHbase s) ≫ l₂.hbase = s.snd
          rw [hl₂base]
          exact (Category.assoc _ _ _).symm.trans
            ((comp_eqToHom_iff _ _ _).mpr (hcBH.fac (sHbase s) WalkingCospan.right))
        have uniq (s : PullbackCone m₁.hbase m₂.hbase)
            (m : s.pt ⟶ baseCone.pt)
            (h₁ : m ≫ baseCone.fst = s.fst)
            (h₂ : m ≫ baseCone.snd = s.snd) : m = liftB s := by
          apply PullbackCone.IsLimit.hom_ext hcBH
          · refine Eq.trans ?_ (hcBH.fac (sHbase s) WalkingCospan.left).symm
            apply (comp_eqToHom_iff P₁.hx _ _).mp
            exact (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) hl₁base).symm.trans h₁)
          · refine Eq.trans ?_ (hcBH.fac (sHbase s) WalkingCospan.right).symm
            apply (comp_eqToHom_iff P₂.hx _ _).mp
            exact (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) hl₂base).symm.trans h₂)
        exact PullbackCone.IsLimit.mk baseCone.condition liftB fac₁ fac₂ uniq
      exact ⟨c, ⟨hc⟩, ⟨hcbase⟩⟩

end

end Deformation
