module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap

/-!
# The fundamental group of an inverse limit of schemes

Let `D : I ⥤ Scheme` be a cofiltered inverse system of quasi-compact and quasi-separated schemes
with affine transition morphisms, let `c` be a limit cone on it, so that `c.pt` is `X = lim Xᵢ`,
and suppose that the schemes of a cofinal tail `Over i₀` of the system are connected. Then `X` is
connected, and for a geometric point `x` of `X` the canonical homomorphisms
`π₁(X, x) ⟶ π₁(Xⱼ, x)`, `j ≤ i₀`, exhibit `π₁(X, x)` as the inverse limit
`lim_{j ≤ i₀} π₁(Xⱼ, x)`, as a topological group.

This is the second conclusion of tag 0BTV; the first, the equivalence of categories
`colim FÉt_{Xᵢ} = FÉt_X`, is in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit` and is what this file rests
on.

## Main definitions

* `AlgebraicGeometry.CompatibleFundamentalGroupFamily` — the compatibility condition cutting the
  inverse limit out of the product of the fundamental groups of the stages of a cofinal tail.
* `AlgebraicGeometry.compatibleFundamentalGroupSubgroup` — that inverse limit, as a subgroup of
  the product.
* `AlgebraicGeometry.etaleFundamentalGroupToCompatibleFamily` — the canonical continuous
  homomorphism from the fundamental group of the limit to the inverse limit, whose coordinates are
  the homomorphisms induced by the projections of the cone.

## Main results

* `AlgebraicGeometry.connectedSpace_of_isLimit_of_connected_tail` — the limit of a cofiltered
  system with a connected cofinal tail is connected, provided it has a geometric point.
* `AlgebraicGeometry.etaleFundamentalGroup_homeomorph_compatibleFamilies` — the canonical map is
  an isomorphism of topological groups: `π₁(X, x) = lim π₁(Xⱼ, x)`.

## Implementation notes

The index category of the cofinal tail is `Over i₀`; the hypothesis that `Xᵢ` is connected for
all sufficiently large `i` is `∀ j : Over i₀, ConnectedSpace (D.obj j.left)`, and the inverse
limit is taken over that tail. Mathlib's `CategoryTheory.Over.initial_forget` and
`CategoryTheory.IsCofiltered.over` make the tail a cofiltered initial subsystem, so the limit cone
restricts to a limit cone over it and the results of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit` apply to the tail as well as
to the whole system.

Connectedness of the limit is proved topologically, from the quasi-compactness statements of
Mathlib's theory of limits with affine transition morphisms: a clopen subset of the limit and its
complement both descend to quasi-compact opens at some stage, which after passing far enough
cover that stage and are disjoint there, so one of them is everything.

The two sides of the comparison are groups of automorphisms of *different* fibre functors — the
fibre functor at `x` on `FÉt_X` and the one at `x` composed with a projection on `FÉt_{Xⱼ}` — and
the geometric point of a stage is the image of `x` under the projection. Composing two projections
therefore gives a geometric point which is only *equal*, not syntactically identical, to a third,
so the compatibility of a family is stated with `HEq`; the lemmas
`AlgebraicGeometry.etaleFundamentalGroup_heq_one`, `_heq_mul` and `_heq_inv` are what makes the
compatible families a subgroup regardless.

Surjectivity of the comparison is where the equivalence of categories enters: an automorphism of
the fibre functor at `x` is built from a compatible family by prescribing its value on each
base-changed cover, which determines it because every cover of `X` comes from a stage, and the
prescription is natural because every morphism of covers comes from a stage too. Injectivity is
the same essential surjectivity, applied to two automorphisms agreeing on all base-changed covers.
Finally the bijection is a homeomorphism because `π₁(X, x)` is compact and the inverse limit is
Hausdorff, both by finiteness of the geometric fibres.

## References

* [Stacks Project, Tag 0BTV](https://stacks.math.columbia.edu/tag/0BTV)
* [Stacks Project, Tag 0BNC](https://stacks.math.columbia.edu/tag/0BNC)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Connectedness of the limit -/

/-- The transition morphisms of the restriction of a system to a tail are affine. -/
private instance isAffineHom_map_forget_comp {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] (i₀ : I) {i j : Over i₀} (f : i ⟶ j) :
    IsAffineHom ((Over.forget i₀ ⋙ D).map f) :=
  inferInstanceAs (IsAffineHom (D.map f.left))

/-- The stages of the restriction of a system to a tail are quasi-compact. -/
private instance compactSpace_obj_forget_comp {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] (i₀ : I) (i : Over i₀) :
    CompactSpace ((Over.forget i₀ ⋙ D).obj i) :=
  inferInstanceAs (CompactSpace (D.obj i.left))

/-- The stages of the restriction of a system to a tail are quasi-separated. -/
private instance quasiSeparatedSpace_obj_forget_comp {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ i : I, QuasiSeparatedSpace (D.obj i)] (i₀ : I) (i : Over i₀) :
    QuasiSeparatedSpace ((Over.forget i₀ ⋙ D).obj i) :=
  inferInstanceAs (QuasiSeparatedSpace (D.obj i.left))

/-- The stages of the restriction of a system to a tail are connected. -/
private instance connectedSpace_obj_forget_comp {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i₀ : I) [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)]
    (i : Over i₀) : ConnectedSpace ((Over.forget i₀ ⋙ D).obj i) :=
  hconn i

/-- The vertex of a whiskered cone is the vertex of the original cone. -/
private instance connectedSpace_whisker_pt {I : Type u} [Category.{u} I] {J : Type u}
    [Category.{u} J] (D : I ⥤ Scheme.{u}) (c : Cone D) (F : J ⥤ I) [ConnectedSpace c.pt] :
    ConnectedSpace (c.whisker F).pt :=
  inferInstanceAs (ConnectedSpace c.pt)

/-- The limit of a cofiltered system of quasi-compact, quasi-separated and preconnected schemes
with affine transition morphisms is preconnected. -/
theorem preconnectedSpace_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i : I, PreconnectedSpace (D.obj i)] : PreconnectedSpace c.pt := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  apply preconnectedSpace_iff_clopen.mpr
  intro S hS
  let U : c.pt.Opens := ⟨S, hS.2⟩
  let V : c.pt.Opens := ⟨Sᶜ, hS.1.isOpen_compl⟩
  obtain ⟨i, Ui, hUi, eUi⟩ := exists_preimage_eq D c hc U hS.1.isCompact
  obtain ⟨j, Vj, hVj, eVj⟩ := exists_preimage_eq D c hc V hS.2.isClosed_compl.isCompact
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Uk := D.map a ⁻¹ᵁ Ui
  let Vk := D.map b ⁻¹ᵁ Vj
  have eUk : c.π.app k ⁻¹ᵁ Uk = U := by
    rw [← Scheme.Hom.comp_preimage, c.w a, eUi]
  have eVk : c.π.app k ⁻¹ᵁ Vk = V := by
    rw [← Scheme.Hom.comp_preimage, c.w b, eVj]
  have hUk : IsCompact (Uk : Set (D.obj k)) :=
    QuasiCompact.isCompact_preimage (f := D.map a) _ Ui.2 hUi
  have hVk : IsCompact (Vk : Set (D.obj k)) :=
    QuasiCompact.isCompact_preimage (f := D.map b) _ Vj.2 hVj
  have hcov : c.π.app k ⁻¹ᵁ (Uk ⊔ Vk) = ⊤ := by
    rw [Scheme.Hom.preimage_sup, eUk, eVk]
    ext x
    simp [U, V]
  have hdis : c.π.app k ⁻¹ᵁ (Uk ⊓ Vk) ≤ c.π.app k ⁻¹ᵁ ⊥ := by
    rw [Scheme.Hom.preimage_inf, eUk, eVk]
    intro x hx
    exact (hx.2 hx.1).elim
  obtain ⟨l, d, hd⟩ := exists_map_eq_top D c hc (Uk ⊔ Vk) hcov
  obtain ⟨m, e, he⟩ := exists_map_preimage_le_map_preimage D c hc
    (QuasiSeparatedSpace.inter_isCompact _ _ Uk.2 hUk Vk.2 hVk) hdis
  obtain ⟨n, p, q, hpq⟩ := IsCofiltered.cospan d e
  let r := p ≫ d
  let Un := D.map r ⁻¹ᵁ Uk
  let Vn := D.map r ⁻¹ᵁ Vk
  have hUn : c.π.app n ⁻¹ᵁ Un = U := by
    rw [← Scheme.Hom.comp_preimage, c.w r, eUk]
  have hVn : c.π.app n ⁻¹ᵁ Vn = V := by
    rw [← Scheme.Hom.comp_preimage, c.w r, eVk]
  have hcover : Un ⊔ Vn = ⊤ := by
    show (D.map (p ≫ d) ⁻¹ᵁ Uk) ⊔ (D.map (p ≫ d) ⁻¹ᵁ Vk) = ⊤
    rw [← Scheme.Hom.preimage_sup, D.map_comp, Scheme.Hom.comp_preimage, hd]
    rfl
  have hdisjoint : Un ⊓ Vn ≤ ⊥ := by
    show (D.map (p ≫ d) ⁻¹ᵁ Uk) ⊓ (D.map (p ≫ d) ⁻¹ᵁ Vk) ≤ ⊥
    rw [← Scheme.Hom.preimage_inf, hpq, D.map_comp, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono (D.map q) he
  have H := (isPreconnected_iff_subset_of_disjoint.mp
    (isPreconnected_univ : _root_.IsPreconnected (Set.univ : Set (D.obj n))))
    Un Vn Un.2 Vn.2 (by exact hcover.ge)
    (by simpa using Set.eq_empty_iff_forall_notMem.mpr (fun x hx ↦ hdisjoint hx))
  rcases H with H | H
  · right
    have ht : Un = ⊤ := top_unique H
    rw [ht] at hUn
    exact (congrArg (fun W : c.pt.Opens ↦ (W : Set c.pt)) hUn).symm
  · left
    have ht : Vn = ⊤ := top_unique H
    rw [ht] at hVn
    have hv : Sᶜ = Set.univ :=
      (congrArg (fun W : c.pt.Opens ↦ (W : Set c.pt)) hVn).symm
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyn : y ∈ Sᶜ := hv.symm ▸ Set.mem_univ y
    exact hyn hy

/-- **The limit of a system with a connected cofinal tail is connected.** If the schemes `D.obj j`
for `j` in the cofinal tail `Over i₀` are connected and the limit has a geometric point, hence is
nonempty, then the limit is connected. -/
theorem connectedSpace_of_isLimit_of_connected_tail {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i₀ : I) [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)]
    (x : GeometricPoint c.pt) : ConnectedSpace c.pt := by
  have : PreconnectedSpace c.pt :=
    preconnectedSpace_of_isLimit (Over.forget i₀ ⋙ D) (c.whisker (Over.forget i₀))
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)
  exact ⟨⟨x.hom default⟩⟩

/-! ### Automorphisms of a functor determined on an essentially surjective family -/

/-- Naturality of a natural automorphism of a set-valued functor, applied to an element. -/
private theorem aut_naturality_apply {C : Type*} [Category* C]
    (F : C ⥤ Type u) (σ : Aut F) {A B : C} (f : A ⟶ B) (p : F.obj A) :
    (σ.app B).hom (F.map f p) = F.map f ((σ.app A).hom p) :=
  congrFun (congrArg (fun k ↦ k.hom) (σ.hom.naturality f)) p

/-- A natural automorphism of a set-valued functor can be prescribed on a family of objects
meeting every isomorphism class: a family of automorphisms of the values, commuting with every
morphism between members of the family, extends to a natural automorphism. -/
private theorem exists_aut_of_essSurj_family {C : Type*} [Category* C] (F : C ⥤ Type u)
    {J : Type*} (A : J → C) (hA : ∀ X, ∃ j, Nonempty (X ≅ A j))
    (s : ∀ j, F.obj (A j) ≅ F.obj (A j))
    (hs : ∀ i j (f : A i ⟶ A j), F.map f ≫ (s j).hom = (s i).hom ≫ F.map f) :
    ∃ σ : Aut F, ∀ j, σ.app (A j) = s j := by
  classical
  choose j e using hA
  let E (X : C) : X ≅ A (j X) := Classical.choice (e X)
  let t (X : C) : F.obj X ≅ F.obj X := F.mapIso (E X) ≪≫ s (j X) ≪≫ (F.mapIso (E X)).symm
  have ht (X Y : C) (f : X ⟶ Y) : F.map f ≫ (t Y).hom = (t X).hom ≫ F.map f := by
    have h := hs (j X) (j Y) ((E X).inv ≫ f ≫ (E Y).hom)
    dsimp [t]
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    calc
      _ = F.map (E X).hom ≫ (F.map (E X).inv ≫ F.map f ≫ F.map (E Y).hom ≫
          (s (j Y)).hom) ≫ F.map (E Y).inv := by simp
      _ = _ := by rw [h]; simp
  let σ : Aut F := NatIso.ofComponents t (fun f ↦ ht _ _ f)
  refine ⟨σ, fun k ↦ ?_⟩
  apply Iso.ext
  have h := hs (j (A k)) k (E (A k)).inv
  dsimp [σ, t]
  rw [← h]
  simp

/-- Two natural automorphisms of a set-valued functor agreeing on a family of objects meeting
every isomorphism class are equal. -/
private theorem aut_ext_of_essSurj_family {C : Type*} [Category* C] (F : C ⥤ Type u)
    {J : Type*} (A : J → C) (hA : ∀ X, ∃ j, Nonempty (X ≅ A j))
    {σ τ : Aut F} (h : ∀ j, σ.app (A j) = τ.app (A j)) : σ = τ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨j, ⟨e⟩⟩ := hA X
  apply (cancel_mono (F.map e.hom)).mp
  rw [← σ.hom.naturality, ← τ.hom.naturality]
  exact congrArg (fun t : F.obj (A j) ≅ F.obj (A j) ↦ F.map e.hom ≫ t.hom) (h j)

/-! ### The action of an induced homomorphism on geometric fibres -/

/-- The fibre projection of `AlgebraicGeometry.finiteEtaleFiberProjection` is natural in the
cover. -/
private theorem finiteEtaleFiberProjection_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : GeometricPoint X) {V W : FiniteEtaleOver Y} (g : V ⟶ W)
    (p : finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V)) :
    finiteEtaleFiberProjection f x W
        ((finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChange f).map g) p) =
      (finiteEtaleFiberFunctor (x.map f)).map g (finiteEtaleFiberProjection f x V p) := by
  apply Subtype.ext
  show (p.1 ≫ ((finiteEtaleBaseChange f).map g).left) ≫ pullback.fst W.hom f
      = (p.1 ≫ pullback.fst V.hom f) ≫ g.left
  calc (p.1 ≫ ((finiteEtaleBaseChange f).map g).left) ≫ pullback.fst W.hom f
      = p.1 ≫ ((finiteEtaleBaseChange f).map g).left ≫ pullback.fst W.hom f :=
        Category.assoc _ _ _
    _ = p.1 ≫ pullback.fst V.hom f ≫ g.left :=
        congrArg (p.1 ≫ ·) (finiteEtaleBaseChange_map_left_fst f g)
    _ = (p.1 ≫ pullback.fst V.hom f) ≫ g.left := (Category.assoc _ _ _).symm

/-- The fibre projection of a base-changed finite étale cover is a bijection, stated for the
projection rather than for the bijection
`AlgebraicGeometry.finiteEtaleFiberProjectionEquiv` carrying it. -/
private theorem finiteEtaleFiberProjection_bijective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : GeometricPoint X) (V : FiniteEtaleOver Y) :
    Function.Bijective (finiteEtaleFiberProjection f x V) :=
  (finiteEtaleFiberProjectionEquiv f x V).bijective

/-- **How an induced homomorphism acts on a fibre.** Let `f : X ⟶ Y` be a morphism of connected
schemes, `x` a geometric point of `X`, `V` a finite étale cover of `X` and `W` one of `Y`, and let
`g : V.left ⟶ W.left` be a morphism over `f`. Then the automorphism induced by
`σ ∈ π₁(X, x)` on the fibre of `W` at `x ∘ f` is computed from the action of `σ` on the fibre of
`V` by composing with `g`. -/
private theorem etaleFundamentalGroupMap_action {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X) (σ : EtaleFundamentalGroup X x)
    (V : FiniteEtaleOver X) (W : FiniteEtaleOver Y) (g : V.left ⟶ W.left)
    (hg : g ≫ W.hom = V.hom ≫ f) (p : finiteEtaleFiber x V) :
    ((σ.app V).hom p).1 ≫ g =
      (((etaleFundamentalGroupMap f x σ).app W).hom
        ⟨p.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, p.2]; rfl⟩).1 := by
  let k : V ⟶ (finiteEtaleBaseChange f).obj W :=
    MorphismProperty.Over.homMk (pullback.lift g V.hom hg) (pullback.lift_snd _ _ _) (by trivial)
  have hk : k.left ≫ pullback.fst W.hom f = g := pullback.lift_fst _ _ _
  have key : ∀ z : finiteEtaleFiber x V,
      (finiteEtaleFiberProjection f x W ((finiteEtaleFiberFunctor x).map k z)).1 = z.1 ≫ g := by
    intro z
    show (z.1 ≫ k.left) ≫ pullback.fst W.hom f = z.1 ≫ g
    exact (Category.assoc _ _ _).trans (congrArg (z.1 ≫ ·) hk)
  have h := etaleFundamentalGroupMap_finiteEtaleFiberProjection f x W σ
    ((finiteEtaleFiberFunctor x).map k p)
  rw [aut_naturality_apply (finiteEtaleFiberFunctor x) σ k p] at h
  have hq : finiteEtaleFiberProjection f x W ((finiteEtaleFiberFunctor x).map k p)
      = (⟨p.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, p.2]; rfl⟩ :
        finiteEtaleFiber (x.map f) W) := Subtype.ext (key p)
  rw [hq] at h
  exact (key ((σ.app V).hom p)).symm.trans (congrArg Subtype.val h)

/-- `AlgebraicGeometry.etaleFundamentalGroupMap_action`, with the induced automorphism given only
up to the heterogeneous equality through which compatible families are stated. -/
private theorem etaleFundamentalGroupMap_action_of_heq {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X) (y : GeometricPoint Y)
    (hy : x.map f = y) (σ : EtaleFundamentalGroup X x) (τ : EtaleFundamentalGroup Y y)
    (hτ : HEq (etaleFundamentalGroupMap f x σ) τ)
    (V : FiniteEtaleOver X) (W : FiniteEtaleOver Y) (g : V.left ⟶ W.left)
    (hg : g ≫ W.hom = V.hom ≫ f)
    (p : finiteEtaleFiber x V) (q : finiteEtaleFiber y W) (hpq : HEq (p.1 ≫ g) q.1) :
    HEq (((σ.app V).hom p).1 ≫ g) (((τ.app W).hom q).1) := by
  subst y
  obtain rfl := eq_of_heq hτ
  obtain rfl : q = ⟨p.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, p.2]; rfl⟩ :=
    Subtype.ext (eq_of_heq hpq).symm
  exact heq_of_eq (etaleFundamentalGroupMap_action f x σ V W g hg p)

/-- The homomorphisms induced on fundamental groups compose: a commuting triangle of morphisms of
connected schemes gives a commuting triangle of induced homomorphisms.

The conclusion is a heterogeneous equality because the geometric point `(x.map f).map g` of `Z`
reached in two steps is only *equal*, not syntactically identical, to the point `x.map h` reached
in one. -/
theorem etaleFundamentalGroupMap_triangle {X Y Z : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] [ConnectedSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    (x : GeometricPoint X) (σ : EtaleFundamentalGroup X x) :
    HEq (etaleFundamentalGroupMap g (x.map f) (etaleFundamentalGroupMap f x σ))
      (etaleFundamentalGroupMap h x σ) := by
  subst h
  have hx : (x.map f).map g = x.map (f ≫ g) := by
    cases x
    simp [GeometricPoint.map, Category.assoc]
  generalize ha : etaleFundamentalGroupMap g (x.map f) (etaleFundamentalGroupMap f x σ) = a
  generalize hb : etaleFundamentalGroupMap (f ≫ g) x σ = b
  have he : ∀ (V : FiniteEtaleOver Z) (p : finiteEtaleFiber ((x.map f).map g) V)
      (q : finiteEtaleFiber (x.map (f ≫ g)) V),
      HEq p.1 q.1 → HEq (((a.app V).hom p).1) (((b.app V).hom q).1) := by
    intro V p q hpq
    obtain ⟨r, hr⟩ := (finiteEtaleFiberProjection_bijective g (x.map f) V).2 p
    obtain ⟨s, hs⟩ := (finiteEtaleFiberProjection_bijective f x
      ((finiteEtaleBaseChange g).obj V)).2 r
    have h₁ := etaleFundamentalGroupMap_action f x σ _ _ (pullback.fst _ _) pullback.condition s
    have h₂ := etaleFundamentalGroupMap_action g (x.map f) (etaleFundamentalGroupMap f x σ) _ _
      (pullback.fst _ _) pullback.condition r
    have h₃ := etaleFundamentalGroupMap_action (f ≫ g) x σ _ V
      (pullback.fst _ _ ≫ pullback.fst _ _)
      (by
        show (pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g) ≫ V.hom =
          pullback.snd (pullback.snd V.hom g) f ≫ (f ≫ g)
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc]) s
    change _ = (((etaleFundamentalGroupMap f x σ).app _).hom
      (finiteEtaleFiberProjection f x _ s)).1 at h₁
    change _ = (((etaleFundamentalGroupMap g (x.map f) (etaleFundamentalGroupMap f x σ)).app _).hom
      (finiteEtaleFiberProjection g (x.map f) V r)).1 at h₂
    rw [hs] at h₁
    rw [hr, ha] at h₂
    have hs' : s.1 ≫ pullback.fst _ _ = r.1 := congrArg Subtype.val hs
    have hr' : r.1 ≫ pullback.fst _ _ = p.1 := congrArg Subtype.val hr
    have eqs : s.1 ≫ (pullback.fst ((finiteEtaleBaseChange g).obj V).hom f
        ≫ pullback.fst V.hom g) = q.1 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst V.hom g) hs').trans (hr'.trans (eq_of_heq hpq)))
    have eqsq : (⟨s.1 ≫ (pullback.fst ((finiteEtaleBaseChange g).obj V).hom f
          ≫ pullback.fst V.hom g), by rw [eqs]; exact q.2⟩ :
        finiteEtaleFiber (x.map (f ≫ g)) V) = q := Subtype.ext eqs
    apply heq_of_eq
    calc ((a.app V).hom p).1
        = (((etaleFundamentalGroupMap f x σ).app ((finiteEtaleBaseChange g).obj V)).hom r).1
            ≫ pullback.fst V.hom g := h₂.symm
      _ = (((σ.app ((finiteEtaleBaseChange f).obj ((finiteEtaleBaseChange g).obj V))).hom s).1
            ≫ pullback.fst ((finiteEtaleBaseChange g).obj V).hom f) ≫ pullback.fst V.hom g :=
          congrArg (· ≫ pullback.fst V.hom g) h₁.symm
      _ = ((σ.app ((finiteEtaleBaseChange f).obj ((finiteEtaleBaseChange g).obj V))).hom s).1
            ≫ (pullback.fst ((finiteEtaleBaseChange g).obj V).hom f
              ≫ pullback.fst V.hom g) := Category.assoc _ _ _
      _ = _ := h₃
      _ = (((etaleFundamentalGroupMap (f ≫ g) x σ).app V).hom q).1 :=
          congrArg (fun t ↦ (((etaleFundamentalGroupMap (f ≫ g) x σ).app V).hom t).1) eqsq
      _ = ((b.app V).hom q).1 := by rw [hb]
  clear ha hb
  cases hx
  apply heq_of_eq
  apply Iso.ext
  ext V p
  apply Subtype.ext
  exact eq_of_heq (he V p p HEq.rfl)

/-! ### Heterogeneous equality of fundamental-group elements at equal geometric points -/

/-- The units of the fundamental groups at two equal geometric points are heterogeneously
equal. -/
theorem etaleFundamentalGroup_heq_one {X : Scheme.{u}} [ConnectedSpace X]
    {x y : GeometricPoint X} (h : x = y) :
    HEq (1 : EtaleFundamentalGroup X x) (1 : EtaleFundamentalGroup X y) := by
  subst y
  rfl

/-- Multiplication in the fundamental groups at two equal geometric points respects heterogeneous
equality. -/
theorem etaleFundamentalGroup_heq_mul {X : Scheme.{u}} [ConnectedSpace X]
    {x y : GeometricPoint X} (h : x = y)
    {a b : EtaleFundamentalGroup X x} {c d : EtaleFundamentalGroup X y}
    (ha : HEq a c) (hb : HEq b d) : HEq (a * b) (c * d) := by
  subst y
  simpa only [heq_eq_eq] using congrArg₂ (· * ·) (eq_of_heq ha) (eq_of_heq hb)

/-- Inversion in the fundamental groups at two equal geometric points respects heterogeneous
equality. -/
theorem etaleFundamentalGroup_heq_inv {X : Scheme.{u}} [ConnectedSpace X]
    {x y : GeometricPoint X} (h : x = y)
    {a : EtaleFundamentalGroup X x} {b : EtaleFundamentalGroup X y}
    (ha : HEq a b) : HEq a⁻¹ b⁻¹ := by
  subst y
  simpa only [heq_eq_eq] using congrArg Inv.inv (eq_of_heq ha)

/-- The geometric point of a stage obtained from a geometric point of the limit is compatible with
the transition morphisms. -/
theorem geometricPoint_map_cone {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (x : GeometricPoint c.pt) {i j : I} (f : i ⟶ j) :
    (x.map (c.π.app i)).map (D.map f) = x.map (c.π.app j) := by
  cases x
  simp [GeometricPoint.map, Category.assoc, c.w f]

/-! ### The inverse limit of the fundamental groups of a cofinal tail -/

/-- **Compatible families of elements of the fundamental groups of a cofinal tail.** A family of
elements of the fundamental groups of the schemes `D.obj j`, `j : Over i₀`, at the images of a
geometric point of the limit, is compatible when every transition homomorphism takes one
coordinate to the next. -/
def CompatibleFundamentalGroupFamily {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) (i₀ : I) [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)]
    (x : GeometricPoint c.pt)
    (σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left))) : Prop :=
  ∀ {i j : Over i₀} (f : i ⟶ j),
    HEq (etaleFundamentalGroupMap (D.map f.left) (x.map (c.π.app i.left)) (σ i)) (σ j)

/-- **The inverse limit of the fundamental groups of a cofinal tail**, as a subgroup of the
product of those groups. -/
def compatibleFundamentalGroupSubgroup {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) (i₀ : I) [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)]
    (x : GeometricPoint c.pt) :
    Subgroup (∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left))) where
  carrier := {σ | CompatibleFundamentalGroupFamily D c i₀ x σ}
  one_mem' := by
    intro i j f
    change HEq (etaleFundamentalGroupMap _ _ 1) 1
    rw [map_one]
    exact etaleFundamentalGroup_heq_one (geometricPoint_map_cone D c x f.left)
  mul_mem' := by
    intro a b ha hb i j f
    change HEq (etaleFundamentalGroupMap _ _ (a i * b i)) (a j * b j)
    rw [map_mul]
    exact etaleFundamentalGroup_heq_mul (geometricPoint_map_cone D c x f.left) (ha f) (hb f)
  inv_mem' := by
    intro a ha i j f
    change HEq (etaleFundamentalGroupMap _ _ (a i)⁻¹) (a j)⁻¹
    rw [map_inv]
    exact etaleFundamentalGroup_heq_inv (geometricPoint_map_cone D c x f.left) (ha f)

/-- **The canonical map to the inverse limit.** The continuous homomorphism from the fundamental
group of the limit to the inverse limit of the fundamental groups of a connected cofinal tail
whose coordinate at `j` is the homomorphism induced by the projection `c.π.app j.left`. -/
def etaleFundamentalGroupToCompatibleFamily {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) [ConnectedSpace c.pt] (i₀ : I)
    [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)] (x : GeometricPoint c.pt) :
    EtaleFundamentalGroup c.pt x →ₜ* compatibleFundamentalGroupSubgroup D c i₀ x := by
  letI (j : I) : ConnectedSpace (((Functor.const I).obj c.pt).obj j) :=
    inferInstanceAs (ConnectedSpace c.pt)
  exact {
    toFun σ := ⟨fun j ↦ etaleFundamentalGroupMap (c.π.app j.left) x σ,
      fun {i j} f ↦ etaleFundamentalGroupMap_triangle (c.π.app i.left) (D.map f.left)
        (c.π.app j.left) (c.w f.left) x σ⟩
    map_one' := by ext j; exact map_one _
    map_mul' a b := by ext j; exact map_mul _ a b
    continuous_toFun := (continuous_pi fun j ↦
      map_continuous (etaleFundamentalGroupMap (c.π.app j.left) x)).subtype_mk _ }

/-- The coordinates of `AlgebraicGeometry.etaleFundamentalGroupToCompatibleFamily` are the
homomorphisms induced by the projections of the cone. -/
theorem etaleFundamentalGroupToCompatibleFamily_coe_apply {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) [ConnectedSpace c.pt] (i₀ : I)
    [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)] (x : GeometricPoint c.pt)
    (σ : EtaleFundamentalGroup c.pt x) (j : Over i₀) :
    (etaleFundamentalGroupToCompatibleFamily D c i₀ x σ).1 j =
      @etaleFundamentalGroupMap c.pt (D.obj j.left) inferInstance (hconn j)
        (c.π.app j.left) x σ :=
  rfl

/-! ### Descent of covers and of morphisms of covers along a cofinal tail -/

/-- The comparison isomorphism of `AlgebraicGeometry.finiteEtaleLimitCompIso`, read at a cover as
an isomorphism from the two-step base change to the one-step base change. -/
private abbrev limitCompIsoApp {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (e : j ⟶ i) (V : FiniteEtaleOver (D.obj i)) :
    (finiteEtaleBaseChange (c.π.app j)).obj ((finiteEtaleBaseChange (D.map e)).obj V) ≅
      (finiteEtaleBaseChange (c.π.app i)).obj V :=
  ((finiteEtaleLimitCompIso D c e).app V).symm

/-- The comparison isomorphism is compatible with the projections to the original cover. -/
private theorem limitCompIsoApp_hom_left_fst {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) {i j : I} (e : j ⟶ i) (V : FiniteEtaleOver (D.obj i)) :
    (limitCompIsoApp D c e V).hom.left ≫ pullback.fst V.hom (c.π.app i) =
      pullback.fst (pullback.snd V.hom (D.map e)) (c.π.app j) ≫ pullback.fst V.hom (D.map e) := by
  have hproj := finiteEtaleBaseChangeComp_hom_app_left_proj (c.π.app j) (D.map e) (c.π.app i)
    (c.w e).symm V
  have hinv : ((finiteEtaleLimitCompIso D c e).inv.app V).left
      ≫ ((finiteEtaleLimitCompIso D c e).hom.app V).left = 𝟙 _ := by
    rw [← MorphismProperty.Comma.comp_left, ← NatTrans.comp_app, Iso.inv_hom_id]
    rfl
  show ((finiteEtaleLimitCompIso D c e).inv.app V).left ≫ pullback.fst V.hom (c.π.app i) = _
  rw [show pullback.fst V.hom (c.π.app i) = finiteEtaleBaseChangeProj (c.π.app i) V from rfl,
    ← hproj, ← Category.assoc, ← Category.assoc, hinv, Category.id_comp]
  rfl

/-- **Every morphism of base-changed covers comes from a stage**, stated against the comparison
isomorphism `AlgebraicGeometry.finiteEtaleLimitCompIso` read at the two covers. -/
private theorem exists_finiteEtale_hom_model_iso {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (A B : FiniteEtaleOver (D.obj i))
    (ψ : (finiteEtaleBaseChange (c.π.app i)).obj A ⟶ (finiteEtaleBaseChange (c.π.app i)).obj B) :
    ∃ (j : I) (e : j ⟶ i)
      (χ : (finiteEtaleBaseChange (D.map e)).obj A ⟶ (finiteEtaleBaseChange (D.map e)).obj B),
      (limitCompIsoApp D c e A).hom ≫ ψ =
        (finiteEtaleBaseChange (c.π.app j)).map χ ≫ (limitCompIsoApp D c e B).hom := by
  obtain ⟨j, e, χ, hχ⟩ := exists_finiteEtale_hom_model D c hc i A B ψ
  refine ⟨j, e, χ, ?_⟩
  have h₁ : (limitCompIsoApp D c e A).hom ≫ (finiteEtaleLimitCompIso D c e).hom.app A = 𝟙 _ :=
    Iso.inv_hom_id ((finiteEtaleLimitCompIso D c e).app A)
  have h₂ : (limitCompIsoApp D c e B).hom = (finiteEtaleLimitCompIso D c e).inv.app B := rfl
  rw [hχ, ← Category.assoc, h₁, Category.id_comp, h₂]

/-- Every finite étale cover of the limit is the base change of a cover of a stage *of a given
cofinal tail*. -/
private theorem exists_finiteEtale_model_on_tail {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] (i₀ : I) (V : FiniteEtaleOver c.pt) :
    ∃ (i : Over i₀) (W : FiniteEtaleOver (D.obj i.left)),
      Nonempty (V ≅ (finiteEtaleBaseChange (c.π.app i.left)).obj W) := by
  exact exists_finiteEtale_model (Over.forget i₀ ⋙ D) (c.whisker (Over.forget i₀))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc) V

/-! ### Injectivity of the canonical map -/

private theorem etaleFundamentalGroupToCompatibleFamily_injective_of_models {I : Type u}
    [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) [ConnectedSpace c.pt] (i₀ : I)
    [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)] (x : GeometricPoint c.pt)
    (hmodel : ∀ V : FiniteEtaleOver c.pt, ∃ (i : Over i₀) (W : FiniteEtaleOver (D.obj i.left)),
      Nonempty (V ≅ (finiteEtaleBaseChange (c.π.app i.left)).obj W)) :
    Function.Injective (etaleFundamentalGroupToCompatibleFamily D c i₀ x) := by
  let (j : I) : ConnectedSpace (((Functor.const I).obj c.pt).obj j) :=
    inferInstanceAs (ConnectedSpace c.pt)
  intro σ τ h
  apply aut_ext_of_essSurj_family (finiteEtaleFiberFunctor x)
    (fun p : Σ i : Over i₀, FiniteEtaleOver (D.obj i.left) ↦
      (finiteEtaleBaseChange (c.π.app p.1.left)).obj p.2)
  · intro V
    obtain ⟨i, W, hW⟩ := hmodel V
    exact ⟨⟨i, W⟩, hW⟩
  · rintro ⟨i, W⟩
    apply Iso.ext
    ext p
    apply (finiteEtaleFiberProjection_bijective (c.π.app i.left) x W).1
    have hi := congrArg (fun a : compatibleFundamentalGroupSubgroup D c i₀ x ↦ a.1 i) h
    change etaleFundamentalGroupMap (c.π.app i.left) x σ =
      etaleFundamentalGroupMap (c.π.app i.left) x τ at hi
    exact (etaleFundamentalGroupMap_finiteEtaleFiberProjection (c.π.app i.left) x W σ p).trans
      ((congrArg (fun a ↦ (a.app W).hom
        (finiteEtaleFiberProjection (c.π.app i.left) x W p)) hi).trans
        (etaleFundamentalGroupMap_finiteEtaleFiberProjection (c.π.app i.left) x W τ p).symm)

private theorem etaleFundamentalGroupToCompatibleFamily_injective {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [ConnectedSpace c.pt] (i₀ : I)
    [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)] (x : GeometricPoint c.pt) :
    Function.Injective (etaleFundamentalGroupToCompatibleFamily D c i₀ x) :=
  etaleFundamentalGroupToCompatibleFamily_injective_of_models D c i₀ x
    (exists_finiteEtale_model_on_tail D c hc i₀)

/-! ### Surjectivity of the canonical map -/

/-- The automorphism of the fibre of a base-changed cover prescribed by an element of the
fundamental group of the stage, through the fibre projections. -/
private def pullbackFiberAut {X Y : Scheme.{u}} (f : X ⟶ Y) (x : GeometricPoint X)
    (σ : Aut (finiteEtaleFiberFunctor (x.map f))) (V : FiniteEtaleOver Y) :
    Aut ((finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj V)) :=
  (finiteEtaleFiberProjectionEquiv f x V).toIso ≪≫ σ.app V ≪≫
    (finiteEtaleFiberProjectionEquiv f x V).toIso.symm

private theorem pullbackFiberAut_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : GeometricPoint X) (σ : Aut (finiteEtaleFiberFunctor (x.map f)))
    (V : FiniteEtaleOver Y) (p : finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V)) :
    finiteEtaleFiberProjection f x V ((pullbackFiberAut f x σ V).hom p) =
      (σ.app V).hom (finiteEtaleFiberProjection f x V p) :=
  (finiteEtaleFiberProjectionEquiv f x V).apply_symm_apply _

private theorem pullbackFiberAut_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : GeometricPoint X) (σ : Aut (finiteEtaleFiberFunctor (x.map f)))
    {V W : FiniteEtaleOver Y} (g : V ⟶ W) :
    (finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChange f).map g) ≫
        (pullbackFiberAut f x σ W).hom =
      (pullbackFiberAut f x σ V).hom ≫
        (finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChange f).map g) := by
  ext p
  apply (finiteEtaleFiberProjection_bijective f x W).1
  show finiteEtaleFiberProjection f x W
      ((pullbackFiberAut f x σ W).hom
        ((finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChange f).map g) p)) =
    finiteEtaleFiberProjection f x W
      ((finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChange f).map g)
        ((pullbackFiberAut f x σ V).hom p))
  rw [pullbackFiberAut_projection f x σ W
      ((finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChange f).map g) p),
    finiteEtaleFiberProjection_naturality f x g p,
    finiteEtaleFiberProjection_naturality f x g ((pullbackFiberAut f x σ V).hom p),
    pullbackFiberAut_projection f x σ V p,
    aut_naturality_apply (finiteEtaleFiberFunctor (x.map f)) σ g
      (finiteEtaleFiberProjection f x V p)]

private theorem pullbackFiberAut_naturality_of_square {X A B : Scheme.{u}} [ConnectedSpace A]
    [ConnectedSpace B] (a : X ⟶ A) (b : X ⟶ B) (f : A ⟶ B) (hf : a ≫ f = b)
    (x : GeometricPoint X) (σ : EtaleFundamentalGroup A (x.map a))
    (τ : EtaleFundamentalGroup B (x.map b))
    (hστ : HEq (etaleFundamentalGroupMap f (x.map a) σ) τ)
    (V : FiniteEtaleOver A) (W : FiniteEtaleOver B) (g : V.left ⟶ W.left)
    (hg : g ≫ W.hom = V.hom ≫ f)
    (h : (finiteEtaleBaseChange a).obj V ⟶ (finiteEtaleBaseChange b).obj W)
    (hh : h.left ≫ pullback.fst W.hom b = pullback.fst V.hom a ≫ g) :
    (finiteEtaleFiberFunctor x).map h ≫ (pullbackFiberAut b x τ W).hom =
      (pullbackFiberAut a x σ V).hom ≫ (finiteEtaleFiberFunctor x).map h := by
  have hx : (x.map a).map f = x.map b := by
    cases x
    simp [GeometricPoint.map, Category.assoc, hf]
  ext p
  apply (finiteEtaleFiberProjection_bijective b x W).1
  show finiteEtaleFiberProjection b x W
      ((pullbackFiberAut b x τ W).hom ((finiteEtaleFiberFunctor x).map h p)) =
    finiteEtaleFiberProjection b x W
      ((finiteEtaleFiberFunctor x).map h ((pullbackFiberAut a x σ V).hom p))
  rw [pullbackFiberAut_projection b x τ W ((finiteEtaleFiberFunctor x).map h p)]
  apply Subtype.ext
  have H := etaleFundamentalGroupMap_action_of_heq f (x.map a) (x.map b) hx σ τ hστ V W g hg
    (finiteEtaleFiberProjection a x V p)
    (finiteEtaleFiberProjection b x W ((finiteEtaleFiberFunctor x).map h p))
    (heq_of_eq (show (p.1 ≫ pullback.fst V.hom a) ≫ g
        = (p.1 ≫ h.left) ≫ pullback.fst W.hom b from
      (Category.assoc _ _ _).trans
        ((congrArg (p.1 ≫ ·) hh.symm).trans (Category.assoc _ _ _).symm)))
  rw [← eq_of_heq H]
  have hp := congrArg Subtype.val (pullbackFiberAut_projection a x σ V p)
  change (((pullbackFiberAut a x σ V).hom p).1 ≫ pullback.fst V.hom a) = _ at hp
  show _ = (((pullbackFiberAut a x σ V).hom p).1 ≫ h.left) ≫ pullback.fst W.hom b
  rw [← hp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (((pullbackFiberAut a x σ V).hom p).1 ≫ ·) hh.symm).trans
      (Category.assoc _ _ _).symm)

/-- A commuting square of automorphisms can be transported across an isomorphism on one side and
a morphism on the other. -/
private theorem naturality_of_iso_square {C : Type*} [Category* C] {A B A' B' : C}
    (α : A' ≅ A) (β : B' ⟶ B) (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A) (b : B ⟶ B) (a' : A' ⟶ A') (b' : B' ⟶ B')
    (h : α.hom ≫ f = g ≫ β)
    (ha : α.hom ≫ a = a' ≫ α.hom) (hb : β ≫ b = b' ≫ β)
    (hg : g ≫ b' = a' ≫ g) : f ≫ b = a ≫ f := by
  apply (cancel_epi α.hom).mp
  calc
    α.hom ≫ (f ≫ b) = (g ≫ β) ≫ b := by rw [← Category.assoc, h]
    _ = (g ≫ b') ≫ β := by rw [Category.assoc, hb, ← Category.assoc]
    _ = a' ≫ (g ≫ β) := by rw [hg, Category.assoc]
    _ = α.hom ≫ (a ≫ f) := by rw [← h, ← Category.assoc, ← ha, Category.assoc]

private theorem pullbackFiberAut_naturality_of_descent {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i : I, ConnectedSpace (D.obj i)] (x : GeometricPoint c.pt)
    (σ : ∀ i, EtaleFundamentalGroup (D.obj i) (x.map (c.π.app i)))
    (hσ : ∀ {i j : I} (e : i ⟶ j),
      HEq (etaleFundamentalGroupMap (D.map e) (x.map (c.π.app i)) (σ i)) (σ j))
    (i : I) (V W : FiniteEtaleOver (D.obj i))
    (f : (finiteEtaleBaseChange (c.π.app i)).obj V ⟶ (finiteEtaleBaseChange (c.π.app i)).obj W) :
    (finiteEtaleFiberFunctor x).map f ≫ (pullbackFiberAut (c.π.app i) x (σ i) W).hom =
      (pullbackFiberAut (c.π.app i) x (σ i) V).hom ≫ (finiteEtaleFiberFunctor x).map f := by
  obtain ⟨j, e, g, h⟩ := exists_finiteEtale_hom_model_iso D c hc i V W f
  let F := finiteEtaleFiberFunctor x
  have hα := pullbackFiberAut_naturality_of_square (c.π.app j) (c.π.app i) (D.map e)
    (c.w e) x (σ j) (σ i) (hσ e) _ V (pullback.fst V.hom (D.map e))
    pullback.condition (limitCompIsoApp D c e V).hom (limitCompIsoApp_hom_left_fst D c e V)
  have hβ := pullbackFiberAut_naturality_of_square (c.π.app j) (c.π.app i) (D.map e)
    (c.w e) x (σ j) (σ i) (hσ e) _ W (pullback.fst W.hom (D.map e))
    pullback.condition (limitCompIsoApp D c e W).hom (limitCompIsoApp_hom_left_fst D c e W)
  have hg := pullbackFiberAut_naturality (c.π.app j) x (σ j) g
  exact naturality_of_iso_square (F.mapIso (limitCompIsoApp D c e V))
    (F.map (limitCompIsoApp D c e W).hom) (F.map f)
    (F.map ((finiteEtaleBaseChange (c.π.app j)).map g)) _ _ _ _
    (by simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg F.map h) hα hβ hg

private theorem pullbackFiberAut_naturality_between_stages {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i : I, ConnectedSpace (D.obj i)] (x : GeometricPoint c.pt)
    (σ : ∀ i, EtaleFundamentalGroup (D.obj i) (x.map (c.π.app i)))
    (hσ : ∀ {i j : I} (e : i ⟶ j),
      HEq (etaleFundamentalGroupMap (D.map e) (x.map (c.π.app i)) (σ i)) (σ j))
    (i j : I) (V : FiniteEtaleOver (D.obj i)) (W : FiniteEtaleOver (D.obj j))
    (f : (finiteEtaleBaseChange (c.π.app i)).obj V ⟶ (finiteEtaleBaseChange (c.π.app j)).obj W) :
    (finiteEtaleFiberFunctor x).map f ≫ (pullbackFiberAut (c.π.app j) x (σ j) W).hom =
      (pullbackFiberAut (c.π.app i) x (σ i) V).hom ≫ (finiteEtaleFiberFunctor x).map f := by
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let α := limitCompIsoApp D c a V
  let β := limitCompIsoApp D c b W
  let g := α.hom ≫ f ≫ β.inv
  let F := finiteEtaleFiberFunctor x
  have hα := pullbackFiberAut_naturality_of_square (c.π.app k) (c.π.app i) (D.map a)
    (c.w a) x (σ k) (σ i) (hσ a) _ V (pullback.fst V.hom (D.map a))
    pullback.condition α.hom (limitCompIsoApp_hom_left_fst D c a V)
  have hβ := pullbackFiberAut_naturality_of_square (c.π.app k) (c.π.app j) (D.map b)
    (c.w b) x (σ k) (σ j) (hσ b) _ W (pullback.fst W.hom (D.map b))
    pullback.condition β.hom (limitCompIsoApp_hom_left_fst D c b W)
  have hg := pullbackFiberAut_naturality_of_descent D c hc x σ hσ k _ _ g
  exact naturality_of_iso_square (F.mapIso α) (F.map β.hom) (F.map f) (F.map g) _ _ _ _
    (by simp [g]) hα hβ hg

private theorem exists_etaleFundamentalGroup_of_compatible_stages_of_models {I : Type u}
    [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ i : I, ConnectedSpace (D.obj i)] [ConnectedSpace c.pt] (x : GeometricPoint c.pt)
    (σ : ∀ i, EtaleFundamentalGroup (D.obj i) (x.map (c.π.app i)))
    (hσ : ∀ {i j : I} (e : i ⟶ j),
      HEq (etaleFundamentalGroupMap (D.map e) (x.map (c.π.app i)) (σ i)) (σ j))
    (hmodel : ∀ V : FiniteEtaleOver c.pt, ∃ (i : I) (W : FiniteEtaleOver (D.obj i)),
      Nonempty (V ≅ (finiteEtaleBaseChange (c.π.app i)).obj W))
    (hnat : ∀ (i j : I) (V : FiniteEtaleOver (D.obj i)) (W : FiniteEtaleOver (D.obj j))
      (f : (finiteEtaleBaseChange (c.π.app i)).obj V ⟶
        (finiteEtaleBaseChange (c.π.app j)).obj W),
      (finiteEtaleFiberFunctor x).map f ≫ (pullbackFiberAut (c.π.app j) x (σ j) W).hom =
        (pullbackFiberAut (c.π.app i) x (σ i) V).hom ≫ (finiteEtaleFiberFunctor x).map f) :
    ∃ τ : EtaleFundamentalGroup c.pt x,
      ∀ i, @etaleFundamentalGroupMap c.pt (D.obj i) inferInstance inferInstance
        (c.π.app i) x τ = σ i := by
  let (i : I) : ConnectedSpace (((Functor.const I).obj c.pt).obj i) :=
    inferInstanceAs (ConnectedSpace c.pt)
  let A (p : Σ i, FiniteEtaleOver (D.obj i)) := (finiteEtaleBaseChange (c.π.app p.1)).obj p.2
  obtain ⟨τ, hτ⟩ := exists_aut_of_essSurj_family (finiteEtaleFiberFunctor x) A
    (fun V ↦ by
      obtain ⟨i, W, hW⟩ := hmodel V
      exact ⟨⟨i, W⟩, hW⟩)
    (fun p ↦ pullbackFiberAut (c.π.app p.1) x (σ p.1) p.2)
    (fun p q f ↦ hnat p.1 q.1 p.2 q.2 f)
  refine ⟨τ, fun i ↦ ?_⟩
  apply Iso.ext
  ext V p
  obtain ⟨q, rfl⟩ := (finiteEtaleFiberProjection_bijective (c.π.app i) x V).2 p
  have H := etaleFundamentalGroupMap_finiteEtaleFiberProjection (c.π.app i) x V τ q
  have hτV := hτ ⟨i, V⟩
  change τ.app ((finiteEtaleBaseChange (c.π.app i)).obj V) =
    pullbackFiberAut (c.π.app i) x (σ i) V at hτV
  rw [hτV] at H
  exact H.symm.trans (pullbackFiberAut_projection (c.π.app i) x (σ i) V q)

private theorem etaleFundamentalGroupToCompatibleFamily_surjective_of_models {I : Type u}
    [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) [ConnectedSpace c.pt] (i₀ : I)
    [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)] (x : GeometricPoint c.pt)
    (hmodel : ∀ V : FiniteEtaleOver c.pt, ∃ (i : Over i₀) (W : FiniteEtaleOver (D.obj i.left)),
      Nonempty (V ≅ (finiteEtaleBaseChange (c.π.app i.left)).obj W))
    (hnat : ∀ σ : {σ : ∀ j : Over i₀,
        EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
        CompatibleFundamentalGroupFamily D c i₀ x σ},
      ∀ (i j : Over i₀) (V : FiniteEtaleOver (D.obj i.left))
        (W : FiniteEtaleOver (D.obj j.left))
        (f : (finiteEtaleBaseChange (c.π.app i.left)).obj V ⟶
          (finiteEtaleBaseChange (c.π.app j.left)).obj W),
        (finiteEtaleFiberFunctor x).map f ≫
            (pullbackFiberAut (c.π.app j.left) x (σ.1 j) W).hom =
          (pullbackFiberAut (c.π.app i.left) x (σ.1 i) V).hom ≫
            (finiteEtaleFiberFunctor x).map f) :
    Function.Surjective (etaleFundamentalGroupToCompatibleFamily D c i₀ x) := by
  intro σ
  let E := Over.forget i₀ ⋙ D
  have (i : Over i₀) : ConnectedSpace (E.obj i) := hconn i
  have : ConnectedSpace (c.whisker (Over.forget i₀)).pt := inferInstanceAs (ConnectedSpace c.pt)
  obtain ⟨τ, hτ⟩ := exists_etaleFundamentalGroup_of_compatible_stages_of_models E
    (c.whisker (Over.forget i₀)) x σ.1 σ.2 hmodel (hnat σ)
  refine ⟨τ, ?_⟩
  apply Subtype.ext
  funext i
  rw [etaleFundamentalGroupToCompatibleFamily_coe_apply]
  exact hτ i

/-! ### The comparison is an isomorphism of topological groups -/

private theorem etaleFundamentalGroup_homeomorph_of_bijective {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) [hX : ConnectedSpace c.pt] (i₀ : I)
    [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)] (x : GeometricPoint c.pt)
    (hbij : Function.Bijective (etaleFundamentalGroupToCompatibleFamily D c i₀ x)) :
    ∃ hX' : ConnectedSpace c.pt,
      letI : ConnectedSpace c.pt := hX'
      ∃ hGroup : Group
          {σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
            CompatibleFundamentalGroupFamily D c i₀ x σ},
        letI := hGroup
        ∃ hTopGroup : IsTopologicalGroup
            {σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
              CompatibleFundamentalGroupFamily D c i₀ x σ},
          letI := hTopGroup
          ∃ e : EtaleFundamentalGroup c.pt x ≃ₜ*
              {σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
                CompatibleFundamentalGroupFamily D c i₀ x σ},
            ∀ (σ : EtaleFundamentalGroup c.pt x) (j : Over i₀),
              (e σ).1 j =
                @etaleFundamentalGroupMap _ _ hX' (hconn j) (c.π.app j.left) x σ := by
  refine ⟨hX, ?_⟩
  let hGroup : Group {σ // CompatibleFundamentalGroupFamily D c i₀ x σ} :=
    (inferInstanceAs (Group (compatibleFundamentalGroupSubgroup D c i₀ x)) :
      Group {σ // CompatibleFundamentalGroupFamily D c i₀ x σ})
  refine ⟨hGroup, ?_⟩
  let : Group {σ // CompatibleFundamentalGroupFamily D c i₀ x σ} := hGroup
  let hTopGroup : IsTopologicalGroup {σ // CompatibleFundamentalGroupFamily D c i₀ x σ} :=
    (inferInstanceAs (IsTopologicalGroup (compatibleFundamentalGroupSubgroup D c i₀ x)) :
      IsTopologicalGroup {σ // CompatibleFundamentalGroupFamily D c i₀ x σ})
  refine ⟨hTopGroup, ?_⟩
  let : IsTopologicalGroup {σ // CompatibleFundamentalGroupFamily D c i₀ x σ} := hTopGroup
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  have (i : Over i₀) := forall_finite_finiteEtaleFiberFunctor_obj (x.map (c.π.app i.left))
  let Φ := etaleFundamentalGroupToCompatibleFamily D c i₀ x
  let e := MulEquiv.ofBijective Φ.toMonoidHom hbij
  have hΦ : Continuous Φ := map_continuous Φ
  let H := e.toEquiv.toHomeomorphOfContinuousClosed hΦ hΦ.isClosedMap
  let e' : EtaleFundamentalGroup c.pt x ≃ₜ*
      {σ // CompatibleFundamentalGroupFamily D c i₀ x σ} :=
    { __ := e
      continuous_toFun := H.continuous_toFun
      continuous_invFun := H.continuous_invFun }
  exact ⟨e', fun σ j ↦ etaleFundamentalGroupToCompatibleFamily_coe_apply D c i₀ x σ j⟩

/-- **Stacks Project, Tag 0BTV, second conclusion: `π₁(X, x̄) = lim π₁(Xᵢ, x̄)`.** Let `D` be a
cofiltered inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms, let `c` be a limit cone on it, so that `c.pt` is `X = lim Xᵢ`, and suppose that the
schemes of the cofinal tail `Over i₀` are connected. Then for a geometric point `x` of `X` the
scheme `X` is connected, the compatible families of elements of the fundamental groups of the
stages of the tail form a topological group, and the canonical map is an isomorphism of
topological groups onto it: every coordinate of the isomorphism is the homomorphism induced by
the corresponding projection of the cone. -/
@[stacks 0BTV "π₁(X, x̄) = lim π₁(Xᵢ, x̄) for a connected cofinal tail"]
theorem etaleFundamentalGroup_homeomorph_compatibleFamilies {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i₀ : I) [hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left)]
    (x : GeometricPoint c.pt) :
    ∃ hX : ConnectedSpace c.pt,
      letI : ConnectedSpace c.pt := hX
      ∃ hGroup : Group
          {σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
            CompatibleFundamentalGroupFamily D c i₀ x σ},
        letI := hGroup
        ∃ hTopGroup : IsTopologicalGroup
            {σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
              CompatibleFundamentalGroupFamily D c i₀ x σ},
          letI := hTopGroup
          ∃ e : EtaleFundamentalGroup c.pt x ≃ₜ*
              {σ : ∀ j : Over i₀, EtaleFundamentalGroup (D.obj j.left) (x.map (c.π.app j.left)) //
                CompatibleFundamentalGroupFamily D c i₀ x σ},
            ∀ (σ : EtaleFundamentalGroup c.pt x) (j : Over i₀),
              (e σ).1 j = @etaleFundamentalGroupMap _ _ hX (hconn j) (c.π.app j.left) x σ := by
  let hX : ConnectedSpace c.pt := connectedSpace_of_isLimit_of_connected_tail D c hc i₀ x
  let Φ := etaleFundamentalGroupToCompatibleFamily D c i₀ x
  have hsurj : Function.Surjective Φ := by
    exact etaleFundamentalGroupToCompatibleFamily_surjective_of_models D c i₀ x
      (exists_finiteEtale_model_on_tail D c hc i₀)
      (fun σ i j V W f ↦
        pullbackFiberAut_naturality_between_stages (Over.forget i₀ ⋙ D) (c.whisker (Over.forget i₀))
          ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)
          x σ.1 σ.2 i j V W f)
  exact etaleFundamentalGroup_homeomorph_of_bijective D c i₀ x
    ⟨etaleFundamentalGroupToCompatibleFamily_injective D c hc i₀ x, hsurj⟩

end AlgebraicGeometry

end
