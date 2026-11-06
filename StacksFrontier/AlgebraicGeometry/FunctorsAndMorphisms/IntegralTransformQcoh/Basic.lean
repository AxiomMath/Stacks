module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Integral transforms of quasi-coherent modules

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R`, with `X`
quasi-compact and quasi-separated.  A quasi-coherent module `K` on `X ×_R Y` defines
an integral transform from quasi-coherent modules on `X` to quasi-coherent modules on `Y`.
It is linear over `R` and commutes with arbitrary direct sums.

## Main definitions

* `AlgebraicGeometry.integralTransformFormula` is the pullback--tensor--pushforward functor,
  before restricting its codomain to quasi-coherent modules.
* `AlgebraicGeometry.quasicoherentIntegralTransform` is the resulting functor on
  quasi-coherent modules.
* `AlgebraicGeometry.modulesLinear` is the canonical linear structure induced by the structure
  morphism to `Spec R`, inherited by the full subcategory of quasi-coherent modules.

## Main results

* `AlgebraicGeometry.quasicoherentIntegralTransformData` constructs the integral transform
  together with its canonical comparison with the pullback--tensor--pushforward formula.
* `AlgebraicGeometry.quasiCompact_of_compactSpace` and
  `AlgebraicGeometry.quasiCompact_isStableUnderBaseChange` give quasi-compactness of the
  second projection.
* `AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace` and
  `AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange` give its quasi-separatedness.
* `AlgebraicGeometry.quasicoherentIntegralTransform_additive` states additivity on morphisms.
* `AlgebraicGeometry.quasicoherentIntegralTransform_isLinearOverBase` states its
  `R`-linearity.
* `AlgebraicGeometry.quasicoherentIntegralTransform_preservesDirectSums` states that it
  commutes with arbitrary direct sums.

## Implementation notes

The tensor functor puts `K` in the left tensor factor.  The symmetry of tensor products of
modules canonically identifies this with the displayed formula in the source.  Since the
scalar action of `R` depends on the structure morphism, `modulesLinear` is supplied explicitly
when using `Functor.Linear`. Additivity and preservation of scalars are stated separately.
The comparison is an isomorphism of functors, so functoriality in the input module is retained.
Quasi-coherent modules are Mathlib's full subcategory defined by
`SheafOfModules.isQuasicoherent`. The pushforward assertion follows from
`AlgebraicGeometry.pushforward_isQuasicoherent` applied to the second projection.
The four registered Mathlib results give the two properties of that projection by first
applying the corresponding source-space criterion to `X → Spec R` and then base-changing
along `Y → Spec R`.

## References

* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u
universe uR uC uD vC vD

namespace AlgebraicGeometry

add_to_stacks 0FZB "quasi-compactness: source criterion"
  AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_sga "3 VIB 11.1" "special case" AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_sga "3 VIB 12.9" "special case" AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_sga "4 VI 1.14" "(i), special case" AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_sga "4 VI 1.8" "(iv), special case" AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_sga "4 VI 1.9.1" "(iv), special case" AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_ega "IV 1.2.4" "Case Z = Spec ℤ" AlgebraicGeometry.quasiCompact_of_compactSpace
add_to_stacks 0FZB "quasi-compactness: base change"
  AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_sga "1 VIII 3.3" "quasi-compact clause"
  AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_sga "4 VI 1.9.1" "(ii), special case" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "I 6.3.4" "clause (iv)" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "I 6.6.4" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "III 6.9.1" "partial" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "III 6.9.4" "more general" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "III 7.7.2" "quasi-compactness of f'"
  AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "IV 1.1.2" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "IV 2.3.7" "(i)" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_ega "IV 2.6.4" "necessity in (v)" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
add_to_stacks 0FZB "quasi-separatedness: source criterion"
  AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace
add_to_ega "IV 1.2.2" "(v), special case" AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace
add_to_ega "IV 1.2.3" AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace
add_to_ega "IV 1.2.6" "partial" AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace
add_to_stacks 0FZB "quasi-separatedness: base change"
  AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_sga "4 VI 1.9.1" "(ii), special case"
  AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_ega "IV 1.2.2" AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "(ii)" AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange

/-- The pullback--tensor--pushforward formula associated to a kernel `K`, with codomain the
category of all module sheaves. -/
@[simps! obj map]
noncomputable def integralTransformFormula (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R)))
    (K : (pullback X.hom Y.hom).Modules) :
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤ Y.left.Modules :=
  ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) ⋙
    Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩).obj K ⋙
    Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)

/-- A lift of the pullback--tensor--pushforward formula to quasi-coherent modules. -/
structure IntegralTransformData (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R)))
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) where
  /-- The integral-transform functor on quasi-coherent modules. -/
  functor : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory
  /-- After forgetting quasi-coherence, the functor is canonically the
  pullback--tensor--pushforward formula. -/
  comparison : functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf) ≅
    integralTransformFormula R X Y K.obj

/-- **Stacks Project, Tag 0FZB (the functor).** A quasi-coherent kernel on `X ×_R Y`
defines the pullback--tensor--pushforward functor from quasi-coherent modules on `X` to
quasi-coherent modules on `Y`. -/
@[stacks 0FZB "the functor"]
noncomputable def quasicoherentIntegralTransformData
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    IntegralTransformData R X Y K := by
  let F := integralTransformFormula R X Y K.obj
  have hF : ∀ M, (F.obj M).IsQuasicoherent := by
    intro M
    let : M.obj.IsQuasicoherent := M.property
    have hpb : ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj).IsQuasicoherent :=
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
        (pullback.fst X.hom Y.hom).toLRSHom.toShHom M.obj (by assumption)
    let pb := (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj
    let : pb.IsQuasicoherent := hpb
    let ten := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩).obj K.obj).obj pb
    have hten : ten.IsQuasicoherent := by
      change ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((pullback X.hom
        Y.hom).toRingedSpace)).presheaf, (((pullback X.hom
        Y.hom).toRingedSpace)).IsSheaf⟩).obj (K.obj)).obj (pb))).IsQuasicoherent
      exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent _
        K.obj pb K.property hpb
    exact @AlgebraicGeometry.pushforward_isQuasicoherent _ _ (pullback.snd X.hom Y.hom)
      inferInstance inferInstance ten hten
  let G : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory :=
    ObjectProperty.lift (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf) F hF
  exact ⟨G, ObjectProperty.liftCompιIso _ F hF⟩

attribute [local irreducible] quasicoherentIntegralTransformData

/-- The integral-transform functor associated to `K`. -/
noncomputable abbrev quasicoherentIntegralTransform
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory :=
  (quasicoherentIntegralTransformData R X Y K).functor

/-- The ring map from the base ring to the ring of functions on an open of an `R`-scheme. -/
@[simps!]
noncomputable def baseRingToSections (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (U : X.left.Opensᵒᵖ) :
    R →+* X.left.ringCatSheaf.obj.obj U :=
  ((forget₂ CommRingCat RingCat).map
      ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop) ≫
    X.left.ringCatSheaf.obj.map U.unop.leTop.op).hom

/-- Multiplication by a base scalar, naturally on all module sheaves. -/
@[simps!]
noncomputable def baseScalar (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (r : R) :
    CatCenter (SheafOfModules.{u} X.left.ringCatSheaf) where
  asHom := {
    app M := ⟨{
      app U := by
        letI : CommRing (X.left.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.left.presheaf.obj U))
        exact ModuleCat.ofHom ((baseRingToSections R X U r) •
          LinearMap.id (R := X.left.ringCatSheaf.obj.obj U) (M := M.val.obj U))
      naturality {U V} f := by
        ext x
        change baseRingToSections R X V r • (M.val.map f).hom x =
          (M.val.map f).hom (baseRingToSections R X U r • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun g => RingCat.Hom.hom g
          (((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop).hom r))
          (X.left.ringCatSheaf.obj.map_comp U.unop.leTop.op f) }⟩
    naturality {M N} f := by
      change f ≫ _ = _ ≫ f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      ext x
      exact ((f.val.app U).hom.map_smul _ x).symm }

/-- The action of the base ring on the category of module sheaves. -/
@[simps]
noncomputable def baseRingToCenter (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) :
    R →+* CatCenter (SheafOfModules.{u} X.left.ringCatSheaf) where
  toFun := baseScalar R X
  map_one' := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U 1 • x = x
    simp
  map_mul' r s := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U (r * s) • x =
      baseRingToSections R X U r • (baseRingToSections R X U s • x)
    simp [mul_smul]
  map_zero' := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U 0 • x = 0
    simp
  map_add' r s := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U (r + s) • x =
      baseRingToSections R X U r • x + baseRingToSections R X U s • x
    simp [add_smul]

/-- The canonical linear structure on module sheaves over a scheme over `R`. -/
@[instance_reducible]
noncomputable def modulesLinear (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) : Linear R X.left.Modules :=
  Linear.ofRingMorphism (baseRingToCenter R X)

/-- A left adjoint is linear as soon as its right adjoint is: the unit is natural, so the
image of `r • 𝟙 X` and `r • 𝟙 (F.obj X)` have the same transpose. -/
lemma leftAdjoint_linear_of_rightAdjoint_linear
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Preadditive C] [Preadditive D] (R : Type u) [CommRing R]
    [Linear R C] [Linear R D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [G.Linear R] : F.Linear R := by
  rw [Functor.linear_iff]
  intro X r
  apply (adj.homEquiv X (F.obj X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  calc
    adj.unit.app X ≫ G.map (F.map (r • 𝟙 X)) =
        (𝟭 C).map (r • 𝟙 X) ≫ adj.unit.app X :=
          (adj.unit.naturality (r • 𝟙 X)).symm
    _ = r • adj.unit.app X := by simp
    _ = (r • adj.unit.app X) ≫ 𝟙 (G.obj (F.obj X)) := by simp
    _ = adj.unit.app X ≫ G.map (r • 𝟙 (F.obj X)) := by
          rw [Functor.map_smul, G.map_id]
          simp

section

/-- Rewriting the scalar in a scalar multiplication.  The statement mentions only a bare
ring element and a bare module element, so the motive of the substitution never touches the
projections of a sheaf of rings. -/
private lemma smul_congr_left {A : Type*} [Semiring A] {N : Type*} [AddCommMonoid N]
    [Module A N] {a b : A} (h : a = b) (x : N) : a • x = b • x := by rw [h]

/-- Pushforward along a morphism of `R`-schemes is `R`-linear: the scalar is pulled back
from the base in both spellings, so the comparison is the identity on sections. -/
lemma over_pushforward_linear (R : Type u) [CommRing R]
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    letI := modulesLinear R X
    letI := modulesLinear R Y
    (Scheme.Modules.pushforward f.left).Linear R := by
  let := modulesLinear R X
  let := modulesLinear R Y
  rw [Functor.linear_iff]
  intro M r
  have hbase (U : Y.left.Opensᵒᵖ) :
      ((f.left.toRingCatSheafHom.hom.app U).hom (baseRingToSections R Y U r) :
          X.left.ringCatSheaf.obj.obj (Opposite.op (f.left ⁻¹ᵁ U.unop))) =
        baseRingToSections R X (Opposite.op (f.left ⁻¹ᵁ U.unop)) r := by
    have hY : U.unop ≤ Y.hom ⁻¹ᵁ ⊤ := le_top.trans (le_of_eq Y.hom.preimage_top.symm)
    have hX : (f.left ⁻¹ᵁ U.unop) ≤ X.hom ⁻¹ᵁ ⊤ :=
      le_top.trans (le_of_eq X.hom.preimage_top.symm)
    show (f.left.app U.unop).hom
        ((Y.hom.appLE ⊤ U.unop hY).hom
          ((Scheme.ΓSpecIso (.of R)).inv.hom r)) =
      (X.hom.appLE ⊤ (f.left ⁻¹ᵁ U.unop) hX).hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom r)
    have heq : Y.hom.appLE ⊤ U.unop hY ≫ f.left.app U.unop =
        X.hom.appLE ⊤ (f.left ⁻¹ᵁ U.unop) hX := by
      rw [f.left.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Over.w]
    exact congrArg (fun g : CommRingCat.Hom _ _ =>
      g.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) heq
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  exact (@smul_congr_left
    ↥(X.left.ringCatSheaf.obj.obj (Opposite.op (f.left ⁻¹ᵁ U.unop))) _ _ _ _ _ _
    (hbase U) (show M.val.obj (Opposite.op (f.left ⁻¹ᵁ U.unop)) from x)).symm

/-- Pullback along a morphism of `R`-schemes is `R`-linear, being the left adjoint of the
`R`-linear pushforward. -/
lemma over_pullback_linear (R : Type u) [CommRing R]
    {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    letI := modulesLinear R X
    letI := modulesLinear R Y
    (Scheme.Modules.pullback f.left).Linear R := by
  let := modulesLinear R X
  let := modulesLinear R Y
  let : (Scheme.Modules.pushforward f.left).Linear R := over_pushforward_linear R f
  exact leftAdjoint_linear_of_rightAdjoint_linear R
    (Scheme.Modules.pullbackPushforwardAdjunction f.left)

/-- Tensoring on the left with a fixed module sheaf on an `R`-scheme is `R`-linear: the base
scalar acts on the right-hand tensor factor and the universal map is bilinear. -/
lemma tensorLeft_linear (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (K : SheafOfModules.{u} (ringSheaf X.left)) :
    letI := modulesLinear R X
    (show X.left.Modules ⥤ X.left.Modules from
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.left.presheaf, X.left.IsSheaf⟩).obj K).Linear R := by
  let := modulesLinear R X
  let ten : X.left.Modules ⥤ X.left.Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.left.presheaf, X.left.IsSheaf⟩).obj K
  let univ := Stacks.SheafOfModules.tensorLeftFunctorUniversal X.left.presheaf
    (ringSheafCond X.left) K
  show ten.Linear R
  rw [Functor.linear_iff]
  intro M r
  apply (univ.bijective M (ten.obj M)).injective
  refine (univ.ι.naturality (r • 𝟙 M)).symm.trans ?_
  apply PresheafOfModules.hom_ext
  intro U
  -- `ringSheaf X.left` is `X.left.ringCatSheaf` at the spelling the tensor API is stated
  -- over; writing the tensor product and the scalar action over it keeps the goal
  -- type-correct without a transparency override.
  let : CommRing ((ringSheaf X.left).obj.obj U) :=
    inferInstanceAs (CommRing (X.left.presheaf.obj U))
  -- The scalar `baseRingToSections R X U r` lives in `X.left.ringCatSheaf.obj.obj U`, so the
  -- two module structures it acts through are restated at that spelling, with the structures
  -- taken from the objects rather than searched for again.
  let : Module (X.left.ringCatSheaf.obj.obj U)
      (((SheafOfModules.forget (ringSheaf X.left)).obj M).obj U) :=
    (((SheafOfModules.forget (ringSheaf X.left)).obj M).obj U).isModule
  let : Module (X.left.ringCatSheaf.obj.obj U)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.left.presheaf, X.left.IsSheaf⟩).obj K ⋙
        SheafOfModules.forget (ringSheaf X.left)).obj M).obj U) :=
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.left.presheaf, X.left.IsSheaf⟩).obj K ⋙
      SheafOfModules.forget (ringSheaf X.left)).obj M).obj U).isModule
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro kernelSection moduleSection
  exact Stacks.RingedSpace.map_tmul_smul ((univ.ι.app M).app U).hom
    (baseRingToSections R X U r)
    kernelSection moduleSection

end

/-- Tensoring on the left with a fixed module sheaf on a scheme preserves all colimits. -/
private lemma tensorLeft_preservesColimits_modules (S : Scheme.{u}) (K : S.Modules) :
    PreservesColimitsOfSize.{u, u}
      (show S.Modules ⥤ S.Modules from
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨S.presheaf, S.IsSheaf⟩).obj K) :=
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits _ ⟨S.presheaf, S.IsSheaf⟩ K

/-- The integral transform is additive on morphisms. -/
@[stacks 0FZB "additivity"]
theorem quasicoherentIntegralTransform_additive
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    (quasicoherentIntegralTransform R X Y K).Additive := by
  have hF : (integralTransformFormula R X Y K.obj).Additive := by
    let ι : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        X.left.Modules :=
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf)
    let pb := Scheme.Modules.pullback (pullback.fst X.hom Y.hom)
    let ten : (pullback X.hom Y.hom).Modules ⥤ (pullback X.hom Y.hom).Modules :=
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩).obj K.obj
    let pf := Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)
    let hι : ι.Additive := ⟨by intros; rfl⟩
    let hpb : pb.Additive := inferInstance
    let hten : ten.Additive := by
      let : PreservesColimitsOfSize.{u, u} ten :=
        tensorLeft_preservesColimits_modules _ K.obj
      let : PreservesColimit (Functor.empty.{0} _) ten := by infer_instance
      let : Functor.PreservesZeroMorphisms ten :=
        Functor.preservesZeroMorphisms_of_preserves_initial_object (F := ten)
      let : PreservesBinaryBiproducts ten :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts ten
      exact Functor.additive_of_preservesBinaryBiproducts ten
    let hpf : pf.Additive := inferInstance
    exact inferInstanceAs ((ι ⋙ pb ⋙ ten ⋙ pf).Additive)
  exact @Functor.additive_of_comp_faithful _ _ _ _ _ _ _ _ _
    (quasicoherentIntegralTransformData R X Y K).functor
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf))
    ⟨by intros; rfl⟩
    (@Functor.additive_of_iso _ _ _ _ _ _ _ hF _
      (quasicoherentIntegralTransformData R X Y K).comparison.symm)
    inferInstance

/-- Linearity descends along a faithful linear functor: if `G` is faithful and linear and
`F ⋙ G` is linear, then so is `F`. -/
lemma linear_of_faithful_comp
    {C : Type*} {D : Type*} {E : Type*}
    [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (R : Type u) [CommRing R] [Linear R C] [Linear R D] [Linear R E]
    (F : C ⥤ D) (G : D ⥤ E) [G.Faithful] [G.Linear R] [(F ⋙ G).Linear R] :
    F.Linear R := by
  constructor
  intro A B f r
  apply G.map_injective
  show (F ⋙ G).map (r • f) = G.map (r • F.map f)
  rw [Functor.map_smul, Functor.map_smul]
  rfl

/-- **Stacks Project, Tag 0FZB (linearity).** The integral transform associated to a
quasi-coherent kernel is linear over the base ring. -/
@[stacks 0FZB "R-linearity"]
theorem quasicoherentIntegralTransform_isLinearOverBase
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    (quasicoherentIntegralTransform R X Y K).Linear R := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  let : Linear R X.left.Modules := modulesLinear R X
  let : Linear R Y.left.Modules := modulesLinear R Y
  let T : Over (Spec (.of R)) := Over.mk ((pullback.fst X.hom Y.hom) ≫ X.hom)
  let : Linear R T.left.Modules := modulesLinear R T
  let G := quasicoherentIntegralTransformData R X Y K
  let ιY := ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)
  let hcomp : (G.functor ⋙ ιY).Linear R := by
    refine @Functor.linear_of_iso R _ _ _ _ _ _ _ _ _ _ _ G.comparison.symm ?_
    let ι : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        X.left.Modules :=
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf)
    let pb : X.left.Modules ⥤ T.left.Modules :=
      Scheme.Modules.pullback (pullback.fst X.hom Y.hom)
    let ten : T.left.Modules ⥤ T.left.Modules :=
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩).obj K.obj
    let pf : T.left.Modules ⥤ Y.left.Modules :=
      Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)
    let hι : ι.Linear R :=
      inferInstanceAs (Functor.Linear R
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf)))
    let hpb : pb.Linear R := by
      let p : T ⟶ X := Over.homMk (pullback.fst X.hom Y.hom) (by simp [T])
      exact over_pullback_linear R p
    let hten : ten.Linear R := tensorLeft_linear R T K.obj
    let hpf : pf.Linear R := by
      let q : T ⟶ Y := Over.homMk (pullback.snd X.hom Y.hom) (by
        simpa [T] using pullback.condition.symm)
      show (Scheme.Modules.pushforward q.left).Linear R
      exact over_pushforward_linear R q
    exact inferInstanceAs ((ι ⋙ pb ⋙ ten ⋙ pf).Linear R)
  exact linear_of_faithful_comp R G.functor ιY

open Opposite TopologicalSpace Scheme.Modules

section

private theorem schemePushforward_preservesCoproducts
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (Scheme.Modules.pushforward f) := by
  constructor
  intro F
  refine ⟨?_⟩
  intro c hc
  let pf := Scheme.Modules.pushforward f
  let τ := colimit.post F pf
  let toSheafY : Y.Modules ⥤ TopCat.Sheaf AddCommGrpCat Y.carrier :=
    SheafOfModules.toSheaf Y.ringCatSheaf
  have hτAb : IsIso (toSheafY.map τ) := by
    have hBasis : TopologicalSpace.Opens.IsBasis
        (Set.range (fun U : Y.affineOpens => (U : Y.Opens))) := by
      rw [Subtype.range_coe]
      exact Y.isBasis_affineOpens
    apply TopCat.Sheaf.isIso_iff_isIso_basis hBasis
    intro U
    let V : X.Opens := f ⁻¹ᵁ (U : Y.Opens)
    have hV : IsCompact (V : Set X) := f.isCompact_preimage U.2.isCompact
    let evX := SheafOfModules.evaluation X.ringCatSheaf (op V)
    let evY := SheafOfModules.evaluation Y.ringCatSheaf (op (U : Y.Opens))
    let forgetX := CategoryTheory.forget₂
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}
    let forgetY := CategoryTheory.forget₂
      (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (op (U : Y.Opens)))) AddCommGrpCat.{u}
    let presheafEvalY := (evaluation (TopologicalSpace.Opens Y.carrier)ᵒᵖ AddCommGrpCat).obj
      (op (U : Y.Opens))
    let sheafEvalY : TopCat.Sheaf AddCommGrpCat Y.carrier ⥤ AddCommGrpCat :=
      TopCat.Sheaf.forget AddCommGrpCat Y.carrier ⋙ presheafEvalY
    let evalAfterPush : Y.Modules ⥤ AddCommGrpCat := toSheafY ⋙ sheafEvalY
    have : PreservesColimitsOfShape (Discrete I) evX :=
      Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact X.ringCatSheaf V hV
    have : PreservesColimitsOfShape (Discrete I) forgetX := inferInstance
    have : PreservesColimitsOfShape (Discrete I) (evX ⋙ forgetX) := inferInstance
    have : PreservesColimitsOfShape (Discrete I) evY :=
      Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact Y.ringCatSheaf U
        U.2.isCompact
    have : PreservesColimitsOfShape (Discrete I) forgetY := inferInstance
    have : PreservesColimitsOfShape (Discrete I) evalAfterPush := by
      show PreservesColimitsOfShape (Discrete I) (evY ⋙ forgetY)
      infer_instance
    have : PreservesColimitsOfShape (Discrete I) (pf ⋙ evalAfterPush) := by
      show PreservesColimitsOfShape (Discrete I) (evX ⋙ forgetX)
      infer_instance
    let α := colimit.post (F ⋙ pf) evalAfterPush
    let β := colimit.post F (pf ⋙ evalAfterPush)
    have hα : IsIso α := by
      let : PreservesColimit (F ⋙ pf) evalAfterPush := inferInstance
      infer_instance
    have hβ : IsIso β := by
      let : PreservesColimit F (pf ⋙ evalAfterPush) := inferInstance
      infer_instance
    have hcomp : IsIso (α ≫ evalAfterPush.map τ) := by
      rw [colimit.post_post]
      exact hβ
    show IsIso (evalAfterPush.map τ)
    exact IsIso.of_isIso_comp_left α (evalAfterPush.map τ)
  have hτApp : ∀ U : Y.Opens, IsIso (τ.app U) := fun U =>
    Functor.map_isIso (TopCat.Sheaf.forget AddCommGrpCat Y.carrier ⋙
      (evaluation (TopologicalSpace.Opens Y.carrier)ᵒᵖ AddCommGrpCat).obj (op U))
      (toSheafY.map τ)
  have hτ : IsIso τ := (Scheme.Modules.Hom.isIso_iff_isIso_app).2 hτApp
  let : PreservesColimit F pf := preservesColimit_of_isIso_post (F := F) (G := pf)
  exact ⟨isColimitOfPreserves pf hc⟩

end

/-- **Stacks Project, Tag 0FZB (direct sums).** The integral transform associated to a
quasi-coherent kernel commutes with arbitrary direct sums. -/
@[stacks 0FZB "arbitrary direct sums"]
theorem quasicoherentIntegralTransform_preservesDirectSums
    (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (quasicoherentIntegralTransform R X Y K) := by
  let P₁ := SheafOfModules.isQuasicoherent X.left.ringCatSheaf
  let P₂ := SheafOfModules.isQuasicoherent Y.left.ringCatSheaf
  let : P₁.IsClosedUnderColimitsOfShape (Discrete I) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := Discrete I) X.left
  let : P₂.IsClosedUnderColimitsOfShape (Discrete I) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := Discrete I) Y.left
  let T := quasicoherentIntegralTransformData R X Y K
  let hT : PreservesColimitsOfShape (Discrete I)
      (T.functor ⋙ ObjectProperty.ι P₂) := by
    refine @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _ T.comparison.symm ?_
    let ι₁ : P₁.FullSubcategory ⥤ X.left.Modules := ObjectProperty.ι P₁
    let PB := Scheme.Modules.pullback (pullback.fst X.hom Y.hom)
    let ten : (pullback X.hom Y.hom).Modules ⥤ (pullback X.hom Y.hom).Modules :=
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩).obj K.obj
    let pf := Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)
    let hHasX : HasColimitsOfShape (Discrete I) X.left.Modules := inferInstance
    let hHas₁ : HasColimitsOfShape (Discrete I) P₁.FullSubcategory :=
      hasColimitsOfShape_of_closedUnderColimits (Discrete I) P₁
    let hCreates₁ : CreatesColimitsOfShape (Discrete I) (ObjectProperty.ι P₁) :=
      inferInstance
    let hι : PreservesColimitsOfShape (Discrete I) ι₁ :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I) (ObjectProperty.ι P₁))
    let hPB : PreservesColimitsOfShape (Discrete I) PB := inferInstance
    let : PreservesColimitsOfSize.{u, u} ten :=
      tensorLeft_preservesColimits_modules _ K.obj
    let hten : PreservesColimitsOfShape (Discrete I) ten := inferInstance
    let hpf : PreservesColimitsOfShape (Discrete I) pf :=
      schemePushforward_preservesCoproducts (pullback.snd X.hom Y.hom) I
    exact inferInstanceAs (PreservesColimitsOfShape (Discrete I) (ι₁ ⋙ PB ⋙ ten ⋙ pf))
  exact preservesColimitsOfShape_of_reflects_of_preserves
    T.functor (ObjectProperty.ι P₂)

end AlgebraicGeometry

end
