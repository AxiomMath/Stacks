module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The Olsson--Laszlo situation

This file packages the standing data of Stacks 0D6R: a site `C`, a sheaf of rings `O` on it,
and a weak Serre subcategory `A` of the category of `O`-modules, subject to the assumption
that there is a set `B` of objects of `C` such that

* every object of `C` has a covering whose members lie in `B`, and
* every `V ∈ B` carries an integer `d_V` and a cofinal system of coverings of `V` on whose
  members the cohomology of every module in `A` vanishes in degrees `> d_V`.

## Main definitions

* `Stacks.Cohomology.CofinalCoveringSystem`: a collection of covering families of a fixed
  object that is cofinal under refinement among all covering families of that object.
* `Stacks.Cohomology.moduleCohomology`: the cohomology of a sheaf of modules over an object
  of a site.
* `Stacks.Cohomology.OlssonLaszloSituation`: the standing data and hypotheses above.

## Main results

The tagged structure is the reusable interface for the subsequent Olsson--Laszlo results;
this file proves nothing about it.

## Implementation notes

A covering family of `V` is a `PreZeroHypercover V`; it is a covering exactly when the sieve
it generates belongs to the topology. Cofinality means that every covering family of `V` is
refined by a distinguished one, the refinement being a `PreZeroHypercover.Hom`. Cohomology in
degree `p` is the `p`-th right derived functor of evaluation on the given object, which is
why the structure carries the sheafification and enough-injectives fields: they are what make
those right derived functors exist.

The set of good objects and the cofinal covering systems are stored as chosen witnesses of
the existential statements of the source situation, rather than as existence hypotheses, so
that later results can name them. The cohomological bound is integer-valued while the right
derived functors are indexed by natural numbers, hence the comparison `degreeBound V hV <
(p : ℤ)`.

## References

* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology

universe v u wRing wModule

/-- A cofinal system of covering families of `V`: every member is a covering, and every
covering family of `V` is refined by a member of the system. -/
structure CofinalCoveringSystem {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (V : C) where
  /-- The distinguished covering families. -/
  cov : Set (PreZeroHypercover.{max u v} V)
  /-- Every distinguished family is a covering. -/
  isCover : ∀ 𝒰, cov 𝒰 → 𝒰.sieve₀ ∈ J V
  /-- Every covering family is refined by a distinguished family. -/
  cofinal : ∀ 𝒰 : PreZeroHypercover.{max u v} V, 𝒰.sieve₀ ∈ J V →
    ∃ 𝒱, cov 𝒱 ∧ Nonempty (𝒱.Hom 𝒰)

/-- The `p`-th cohomology of a sheaf of modules over an object of a site, defined as the
`p`-th right derived functor of evaluation on that object. -/
noncomputable def moduleCohomology {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)] (U : C) (p : ℕ)
    (F : SheafOfModules.{wModule} O) : ModuleCat.{wModule} (O.obj.obj (.op U)) := by
  let E : CategoryTheory.Functor (SheafOfModules.{wModule} O)
      (ModuleCat.{wModule} (O.obj.obj (.op U))) := SheafOfModules.evaluation O (.op U)
  let hE : E.Additive := by
    dsimp [E, SheafOfModules.evaluation]
    infer_instance
  exact (@CategoryTheory.Functor.rightDerived _ _ _ _ _ _ _ E hE p).obj F

/-- **Stacks 0D6R.** The standing Olsson--Laszlo situation: a weak Serre subcategory of
modules on a site, together with a locally covering class of objects admitting cofinal
systems of coverings on whose members higher cohomology vanishes uniformly in the module. -/
@[stacks 0D6R]
structure OlssonLaszloSituation where
  /-- The underlying category of the site. -/
  C : Type u
  /-- The category structure of the site. -/
  [category : Category.{v} C]
  /-- The topology of the site. -/
  J : GrothendieckTopology C
  /-- The sheaf of rings. -/
  O : Sheaf J RingCat.{wRing}
  /-- Existence of sheafification in the universe used for modules. -/
  [hasSheafify : HasSheafify J AddCommGrpCat.{wModule}]
  /-- The local-bijection description of weak equivalences used for sheafification. -/
  [wEqualsLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  /-- The weak Serre subcategory, represented by its object property. -/
  A : ObjectProperty (SheafOfModules.{wModule} O)
  /-- The chosen object property is a weak Serre class. -/
  [weakSerre : A.IsWeakSerreClass]
  /-- Sheaves of `O`-modules have enough injectives, so their cohomology is defined. -/
  [enoughInjectives : EnoughInjectives (SheafOfModules.{wModule} O)]
  /-- The collection of objects with controlled cohomology. -/
  B : Set C
  /-- Every object of the site has a covering whose members belong to `B`. -/
  basis_cover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
    𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i)
  /-- The integer cohomological bound attached to an object of `B`. -/
  degreeBound : ∀ V : C, B V → ℤ
  /-- The cofinal system of coverings attached to an object of `B`. -/
  coverings : ∀ V : C, B V → CofinalCoveringSystem J V
  /-- On every member of every distinguished covering, the cohomology of a module in `A`
  vanishes above the bound attached to the covered object. -/
  vanishing : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ (F : SheafOfModules.{wModule} O), A F → IsZero (moduleCohomology O (𝒰.X i) p F)

attribute [instance] OlssonLaszloSituation.category OlssonLaszloSituation.hasSheafify
  OlssonLaszloSituation.wEqualsLocallyBijective OlssonLaszloSituation.weakSerre
  OlssonLaszloSituation.enoughInjectives

end Stacks.Cohomology

-- ===== merged from StacksDraft.Ch21.Sec25.RelativeOlssonLaszloSituation =====

/-!
# The relative Olsson--Laszlo situation

Stacks 0D6V is the relative version of the standing hypothesis of Stacks 0D6R. The data is a
morphism `f : X ⟶ Y` of ringed sites together with a weak Serre subcategory `A` of the
category of modules on `X`, and the hypothesis is that `Y` has a collection `B` of objects
such that every object of `Y` is covered by members of `B`, and every `V ∈ B` carries an
integer bound `d_V` and a cofinal system of coverings of `V` on whose members the cohomology
of every module of `A` — computed on the site of `X`, over the image of the member under the
continuous functor underlying `f` — vanishes in degrees `> d_V`.

## Main definitions

* `Stacks.Cohomology.OlssonLaszloPrimeSituation`: the data and hypotheses above, packaged as
  a structure, in the same style as `Stacks.Cohomology.OlssonLaszloSituation` for 0D6R.

## Implementation notes

Cofinal systems of coverings and the cohomology of a sheaf of modules over an object are
`Stacks.Cohomology.CofinalCoveringSystem` and `Stacks.Cohomology.moduleCohomology` from
0D6R, so that the absolute and relative situations speak about the same notions. Covering
families are `PreZeroHypercover`, and vanishing of a cohomology module is `IsZero`. The
cohomology appearing in the vanishing hypothesis is cohomology on the source site over
`f.u.obj (𝒰.X i)`, as in the source.

Both ringed sites have equal object and morphism universes, as `AlgebraicGeometry.RingedSite.Hom`
requires; this universe is independent of the universe of the section rings and of the
universe of the module sections. The ring sheaf of a ringed site is
`AlgebraicGeometry.RingedSite.ringSheaf`, the structure sheaf with commutativity
forgotten.

The sheafification, local-bijection and enough-injectives fields are the infrastructure that
makes cohomology of modules in the chosen module universe available, exactly as in 0D6R.

## References

* [Stacks Project, Tag 0D6V](https://stacks.math.columbia.edu/tag/0D6V)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology

universe v u wRing wModule

/-- **Stacks 0D6V.** The relative Olsson--Laszlo situation for a morphism of ringed sites:
the target has a locally covering collection of objects carrying cofinal systems of
coverings on whose members the cohomology, on the source site, of the modules of the chosen
weak Serre subcategory vanishes above an object-dependent integer bound. -/
@[stacks 0D6V]
public structure OlssonLaszloPrimeSituation where
  /-- The source ringed site. -/
  X : AlgebraicGeometry.RingedSite.{u, u, wRing}
  /-- The target ringed site. -/
  Y : AlgebraicGeometry.RingedSite.{u, u, wRing}
  /-- The morphism of ringed sites. Its continuous functor goes from `Y.C` to `X.C`. -/
  f : AlgebraicGeometry.RingedSite.Hom X Y
  /-- Existence of sheafification in the universe used for modules. -/
  [hasSheafify : HasSheafify X.J AddCommGrpCat.{wModule}]
  /-- The local-bijection description of the weak equivalences used for sheafification. -/
  [wEqualsLocallyBijective : X.J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  /-- Sheaves of modules on the source have enough injectives, so their cohomology is
  defined. -/
  [enoughInjectives : EnoughInjectives (SheafOfModules.{wModule}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  /-- The weak Serre subcategory of modules on the source ringed site, represented by its
  object property. -/
  A : ObjectProperty (SheafOfModules.{wModule} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  /-- The chosen object property is a weak Serre class. -/
  [weakSerre : A.IsWeakSerreClass]
  /-- The collection of objects of the target site with controlled cohomology. -/
  B : Set Y.C
  /-- Every object of the target site has a covering whose members belong to `B`. -/
  basis_cover : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B (𝒰.X i)
  /-- The integer cohomological bound attached to an object of `B`. -/
  degreeBound : ∀ V : Y.C, B V → ℤ
  /-- The cofinal system of coverings attached to an object of `B`. -/
  coverings : ∀ V : Y.C, B V → CofinalCoveringSystem Y.J V
  /-- On the image under `f` of every member of every distinguished covering, the cohomology
  of a module in `A` vanishes above the bound attached to the covered object. -/
  vanishing : ∀ (V : Y.C) (hV : B V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{wModule} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
        A F → IsZero
          (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj (𝒰.X i)) p F)

attribute [instance] OlssonLaszloPrimeSituation.hasSheafify
  OlssonLaszloPrimeSituation.wEqualsLocallyBijective
  OlssonLaszloPrimeSituation.enoughInjectives OlssonLaszloPrimeSituation.weakSerre


/-! ### Monomorphism criteria for an inverse system indexed by `ℕ`

Both were copied verbatim between `SectionsInjectivity` and `TruncationTowerConvergence`,
which do not import one another. They are stated here, the lowest module both of those
reach, and they speak only of limits and products of an `ℕᵒᵖ`-indexed system. -/

/-- If every transition map `F n ⟶ F N` with `n ≥ N` of an inverse system indexed by `ℕ` is a
monomorphism, then so is the projection from the limit to the stage `N`. -/
theorem mono_limit_projection_of_monos_ge
    {C : Type*} [Category C] {F : ℕᵒᵖ ⥤ C} [HasLimit F] (N : ℕ)
    (htrans : ∀ n (hn : N ≤ n), Mono (F.map (homOfLE hn).op)) :
    Mono (limit.π F ⟨N⟩) := by
  constructor
  intro Z g h e
  have hw : ∀ {a b : ℕᵒᵖ} (f : a ⟶ b) (x : Z ⟶ limit F),
      (x ≫ limit.π F a) ≫ F.map f = x ≫ limit.π F b := fun f x ↦ by
    rw [Category.assoc, limit.w F f]
  apply limit.hom_ext
  intro n
  by_cases hn : N ≤ n.unop
  · exact (cancel_mono (F.map (homOfLE hn).op)).1 (by rw [hw, hw, e])
  · have f := (homOfLE (Nat.le_of_not_ge hn)).op
    rw [← hw f g, ← hw f h, e]

/-- Let `p : L ⟶ ∏ₙ K n` be annihilated by the difference map of an inverse system indexed by
`ℕ`, and let `G` preserve that product and send `p` to a monomorphism. If `G` sends every
transition map `K n ⟶ K N` with `n ≥ N` to a monomorphism, then `G (p ≫ π N)` is a
monomorphism. -/
theorem mono_projection_of_difference
    {D A : Type*} [Category* D] [Preadditive D] [Category* A]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    {L : D} (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : p ≫ (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
        K.map (homOfLE (Nat.le_succ n)).op) = 0)
    (G : D ⥤ A) [PreservesLimit (Discrete.functor (fun n : ℕ ↦ K.obj ⟨n⟩)) G]
    [HasLimit (K ⋙ G)] [Mono (G.map p)]
    (N : ℕ) (hinj : ∀ n (hn : N ≤ n), Mono (G.map (K.map (homOfLE hn).op))) :
    Mono (G.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N)) := by
  let c : Cone K :=
    { pt := L
      π := NatTrans.ofOpSequence (fun n ↦ p ≫ Pi.π _ n) (fun n ↦ by
        have h := congrArg (fun f => f ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n) hp
        simpa [Category.assoc, Preadditive.comp_sub, sub_eq_zero] using h) }
  let q := limit.lift (K ⋙ G) (G.mapCone c)
  have : Mono (limit.π (K ⋙ G) ⟨N⟩) := mono_limit_projection_of_monos_ge N hinj
  have hq : Mono q := by
    constructor
    intro Z f g h
    apply (cancel_mono (G.map p)).1
    apply (isLimitOfPreserves G (productIsProduct (fun n : ℕ ↦ K.obj ⟨n⟩))).hom_ext
    rintro ⟨n⟩
    have hn := congrArg (fun f => f ≫ limit.π (K ⋙ G) ⟨n⟩) h
    simp only [q, Category.assoc, limit.lift_π] at hn
    simpa only [Functor.mapCone_π_app, c, NatTrans.ofOpSequence_app, G.map_comp,
      Category.assoc, Fan.mk_π_app] using hn
  have h : q ≫ limit.π (K ⋙ G) ⟨N⟩ = G.map (p ≫ Pi.π _ N) :=
    limit.lift_π (G.mapCone c) ⟨N⟩
  rw [← h]
  infer_instance

/-! ### The long exact sequence of the derived-limit triangle -/


/-! ### Two further criteria shared by the two truncation-tower modules

Also copied verbatim between `SectionsInjectivity` and `TruncationTowerConvergence`.
These two speak of distinguished triangles and the homology functor of the derived
category, so this section opens `CategoryTheory.Pretriangulated`. -/

/-- If the difference map of the inverse system `K ⋙ G` has vanishing cokernel, then `G` sends
the difference map `∏ₙ K n ⟶ ∏ₙ K n` of `K` to an epimorphism. -/
theorem epi_map_difference
    {D A : Type*} [Category* D] [Preadditive D] [Category* A] [Abelian A]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (G : D ⥤ A) [G.Additive]
    [HasProduct fun n : ℕ ↦ G.obj (K.obj ⟨n⟩)]
    [PreservesLimit (Discrete.functor (fun n : ℕ ↦ K.obj ⟨n⟩)) G]
    (hz : IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ G.obj (K.obj ⟨n⟩)) n -
        Pi.π (fun n : ℕ ↦ G.obj (K.obj ⟨n⟩)) (n + 1) ≫
          G.map (K.map (homOfLE (Nat.le_succ n)).op)))) :
    Epi (G.map (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
        K.map (homOfLE (Nat.le_succ n)).op)) := by
  let d := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op
  let e := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj (K.obj ⟨n⟩)) n -
    Pi.π (fun n : ℕ ↦ G.obj (K.obj ⟨n⟩)) (n + 1) ≫
      G.map (K.map (homOfLE (Nat.le_succ n)).op)
  have : Epi e := Abelian.epi_of_cokernel_π_eq_zero _ (hz.eq_of_tgt _ _)
  have h : G.map d ≫ piComparison G (fun n : ℕ ↦ K.obj ⟨n⟩) =
      piComparison G (fun n : ℕ ↦ K.obj ⟨n⟩) ≫ e := by
    ext n
    simp only [Category.assoc, piComparison_comp_π, e, Pi.lift_comp_π,
      Preadditive.comp_sub, ← G.map_comp, d]
    simp only [G.map_sub, G.map_comp, piComparison_comp_π_assoc]
  exact (epi_comp_iff_of_isIso (G.map d) (piComparison G (fun n : ℕ ↦ K.obj ⟨n⟩))).1 <| by
    rw [h]
    infer_instance


/-- If a presheaf of `O`-modules has vanishing sections on every member of every covering of `V` in
a cofinal system of coverings, then its sheafification has vanishing sections over `V`. -/
theorem sheafification_eval_isZero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    (V : C) (Cov : CofinalCoveringSystem J V)
    (M : PresheafOfModules.{wModule} O.obj)
    (hM : ∀ 𝒰, Cov.cov 𝒰 → ∀ i : 𝒰.I₀, IsZero (M.obj (.op (𝒰.X i)))) :
    IsZero (((PresheafOfModules.sheafification (𝟙 O.obj)).obj M).val.obj (.op V)) := by
  let S := (PresheafOfModules.sheafification (𝟙 O.obj)).obj M
  let η : M.presheaf ⟶ S.val.presheaf := CategoryTheory.toSheafify J M.presheaf
  have hS : Presieve.IsSheaf J (S.val.presheaf ⋙ forget AddCommGrpCat.{wModule}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ S.isSheaf)
  apply ModuleCat.isZero_iff_subsingleton.2
  -- Phrase the carrier as that of the underlying abelian-group presheaf, which is the shape in
  -- which the sheaf condition below is available, so that no section has to be transported
  -- between the two spellings of it.
  change Subsingleton (ToType (S.val.presheaf.obj (.op V)))
  apply subsingleton_of_forall_eq 0
  intro s
  let T := Presheaf.imageSieve η s
  have hT : T ∈ J V := by
    exact Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J M.presheaf) s
  obtain ⟨𝒰, h𝒰, ⟨f⟩⟩ := Cov.cofinal T.arrows.preZeroHypercover (by
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using hT)
  have hle : 𝒰.sieve₀ ≤ T := by
    simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using f.sieve₀_le_sieve₀
  apply (hS _ (Cov.isCover 𝒰 h𝒰)).isSeparatedFor.ext
  intro U g hg
  obtain ⟨W, a, b, ⟨i⟩, hab⟩ := hg
  obtain ⟨t, ht⟩ := hle _ (𝒰.sieve₀_f i)
  have : Subsingleton (ToType (M.presheaf.obj (.op (𝒰.X i)))) :=
    ModuleCat.subsingleton_of_isZero (hM 𝒰 h𝒰 i)
  have hi : S.val.presheaf.map (𝒰.f i).op s = 0 := by
    rw [← ht, Subsingleton.elim t 0]
    exact map_zero _
  change S.val.presheaf.map g.op s = S.val.presheaf.map g.op 0
  rw [← hab, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, hi]
  simp only [map_zero]

/-- If a map of presheaves of `O`-modules is injective on sections over every member of every
covering of `V` in a cofinal system of coverings, then the sheafified map is injective on sections
over `V`. -/
theorem sheafification_eval_mono
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    (V : C) (Cov : CofinalCoveringSystem J V)
    {M N : PresheafOfModules.{wModule} O.obj} (f : M ⟶ N)
    (hf : ∀ 𝒰, Cov.cov 𝒰 → ∀ i : 𝒰.I₀, Mono (f.app (.op (𝒰.X i)))) :
    Mono ((SheafOfModules.evaluation O (.op V)).map
      ((PresheafOfModules.sheafification (𝟙 O.obj)).map f)) := by
  let E := PresheafOfModules.sheafification (𝟙 O.obj) ⋙ SheafOfModules.evaluation O (.op V)
  have hker : ∀ 𝒰, Cov.cov 𝒰 → ∀ i : 𝒰.I₀,
      IsZero ((kernel f).obj (.op (𝒰.X i))) := by
    intro 𝒰 h𝒰 i
    let e := PresheafOfModules.evaluation O.obj (.op (𝒰.X i))
    have : Mono (e.map f) := hf 𝒰 h𝒰 i
    exact IsZero.of_iso (isZero_kernel_of_mono (e.map f)) (PreservesKernel.iso e f)
  have hzero' : IsZero (kernel (E.map f)) :=
    (sheafification_eval_isZero O V Cov (kernel f) hker).of_iso (PreservesKernel.iso E f).symm
  exact Abelian.mono_of_kernel_ι_eq_zero _ (hzero'.eq_of_src _ _)
end Stacks.Cohomology

end
