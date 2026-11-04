module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCoefficientLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposInverseImageTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageComp

/-!
# The direct image along `f`, through the restriction of scalars to `f⁻¹O_Y`

Let `f : (Sh(X), O_X) ⟶ (Sh(Y), O_Y)` be a morphism of ringed topoi and let
`g : (Sh(X), f⁻¹O_Y) ⟶ (Sh(Y), O_Y)` be the morphism of ringed topoi with the same morphism of
topoi and the inverse image of `O_Y` as structure sheaf
(`Stacks.Sheaves.RingedToposModules.RingedToposHom.inverseImageRingedToposHom`). The direct
image of sheaves of modules along `f` is restriction of scalars along the inverse-image form
`f♯ : f⁻¹O_Y ⟶ O_X` of the structure map followed by the direct image along `g`, on the nose.
This file proves that the two lax monoidal structures, each the right adjoint of the monoidal
pullback of Tag 03EL, agree through that restriction: on the image of a pure tensor of local
sections, the tensorator of `f_*` followed by `f_*m` is the tensorator of `g_*` followed by
`g_*m'`, for any `m'` agreeing with `m` on pure tensors (`toposDirectImageModules_μ_comp_map_app`).
This is what identifies the direct image of differential graded modules along `f` with the
restriction of scalars along `f♯` followed by the direct image along `g`, the step of the proof
of Tag 0FSI (2) reading `f^*P = f⁻¹P ⊗_{f⁻¹A} A'` as a pullback over `f⁻¹O_Y`.

## Implementation notes

The tensorator of a direct image has no description on sections; the one available formula is
`Stacks.Sheaves.RingedToposModules.prodComparison_comp_tensorPairing_comp_μ`, a morphism-level
identity of sheaves of sets. It is applied separately at `f` and at `g`, evaluated at a section
of the direct image of the product lifting the given pair of sections, and the two values meet
in the direct image of the canonical pairing, which `f` and `g` share. The two spellings of the
same objects (through `f` and through `g`) are definitionally equal, but unifying morphisms or
pairs built on them across the two spellings does not terminate in reasonable time; every
comparison is therefore made either at an object or on an element, through the small `rfl`
lemmas `prodComparison_inverseImageRingedToposHom`, `prodObjMk_inverseImageRingedToposHom` and
`map_pushforward_map_inverseImageRingedToposHom`, and the statements are routed through
`tensoratorApp`, whose two instances are then unfolded separately.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.RingedToposModules.RingedToposHom
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

open scoped TensorProduct

universe t w v₁ u₁ v₂ u₂ v u

namespace SheafOfModules.DifferentialGradedModule

section Key

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- Sheafification of sheaves of abelian groups on `(Sh(X), f⁻¹O_Y)` is that on `X`. -/
instance hasSheafify_inverseImageRingedTopos_addCommGrpCat :
    HasSheafify (inverseImageRingedTopos f).J AddCommGrpCat.{w} :=
  inferInstanceAs (HasSheafify X.J AddCommGrpCat.{w})

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

/-- A morphism out of a tensor product, followed by the canonical pairing, on a pair of local
sections. -/
theorem sectionsFunctor_map_tensorPairing_comp {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (k : M ⊗ N ⟶ P)
    (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
    (b : (Sheaf.sectionsFunctor X.J U).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :
    (Sheaf.sectionsFunctor X.J U).map (tensorPairing M N ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map k)
          (Functor.prodObjMk a b) =
      k.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U (a ⊗ₜ b)) :=
  (Functor.map_comp_apply _ _ _ _).trans
    (congrArg ((Sheaf.sectionsFunctor X.J U).map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map k))
        (canonicalPairing_apply M N U a b))

/-- **The inverse-image form `f⁻¹O_Y ⟶ O_X` of the structure map of `f`**, as a morphism between
the sheaves of rings underlying `f⁻¹O_Y` and `O_X`. -/
noncomputable abbrev coeffMap :
    toRingCat X.J (inverseImageStructureSheaf f) ⟶ toRingCat X.J X.O :=
  f.fSharpInverseImage

/-- The restriction of scalars of a sheaf of `O_X`-modules to `f⁻¹O_Y`. -/
noncomputable abbrev restrictCoeffMod
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O) :=
  (restrictCoeffSheaf (coeffMap f)).obj M

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}] in
/-- Two morphisms out of tensor products of sheaves of `O_X`-modules and of their restrictions to
`f⁻¹O_Y` which agree on pure tensors of local sections agree after the canonical pairings. -/
theorem tensorPairing_comp_eq
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (m' : restrictCoeffMod f M ⊗ restrictCoeffMod f N ⟶ restrictCoeffMod f P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : (restrictCoeffMod f M).val.obj U)
        (b : (restrictCoeffMod f N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) (restrictCoeffMod f M)
          (restrictCoeffMod f N)).app U (a ⊗ₜ b))) :
    tensorPairing M N ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map m =
      tensorPairing (restrictCoeffMod f M) (restrictCoeffMod f N) ≫
        (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)).map m' :=
  prod_hom_ext_sections fun U a b =>
    (sectionsFunctor_map_tensorPairing_comp m U a b).trans
      ((hm U a b).trans (sectionsFunctor_map_tensorPairing_comp (X := inverseImageRingedTopos f)
        m' U a b).symm)

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}] in
/-- The tensorator followed by the direct image of a morphism out of a tensor product, on the
canonical pairing read through the product comparison, is the direct image of the morphism on
the canonical pairing. -/
theorem prodComparison_comp_tensorPairing_comp_map_μ_comp
    {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P) :
    prodComparison h.toToposHom.pushforward
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
        tensorPairing ((pushforwardModules h).obj M) ((pushforwardModules h).obj N) ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            (Functor.LaxMonoidal.μ (pushforwardModules h) M N ≫ (pushforwardModules h).map m) =
        h.toToposHom.pushforward.map
          (tensorPairing M N ≫
            (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map m) := by
  rw [Functor.map_comp, moduleSheafFunctor_map_pushforwardModules_map, Functor.map_comp,
    ← prodComparison_comp_tensorPairing_comp_μ h M N]
  rfl

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}] in
/-- **The tensorator of a direct image, followed by the direct image of a morphism out of a
tensor product, on a pure tensor of local sections**: it is the direct image of the morphism on
the canonical pairing, evaluated at any section of the direct image of the product lifting the
two sections. -/
theorem μ_comp_map_val_app_tensorSheafUnit
    {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (V : Y.Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor Y.J V).obj (h.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)))
    (a : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj M)))
    (b : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj N)))
    (hz : (Sheaf.sectionsFunctor Y.J V).map (prodComparison h.toToposHom.pushforward
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) z =
        Functor.prodObjMk a b) :
    (Functor.LaxMonoidal.μ (pushforwardModules h) M N ≫ (pushforwardModules h).map m).val.app V
        ((PresheafOfModules.tensorSheafUnit (Osharp := Y.O) ((pushforwardModules h).obj M)
          ((pushforwardModules h).obj N)).app V (a ⊗ₜ b)) =
      (Sheaf.sectionsFunctor Y.J V).map (h.toToposHom.pushforward.map
        (tensorPairing M N ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map m)) z :=
  (sectionsFunctor_map_tensorPairing_comp (X := Y) _ V a b).symm.trans
    ((congrArg ((Sheaf.sectionsFunctor Y.J V).map (tensorPairing ((pushforwardModules h).obj M)
        ((pushforwardModules h).obj N) ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (Functor.LaxMonoidal.μ (pushforwardModules h) M N ≫ (pushforwardModules h).map m)))
      hz.symm).trans
    (((Sheaf.sectionsFunctor Y.J V).map_comp_apply _ _ z).symm.trans
      (congrArg (fun φ => (Sheaf.sectionsFunctor Y.J V).map φ z)
        (prodComparison_comp_tensorPairing_comp_map_μ_comp h m))))

/-- The tensorator of a direct image followed by the direct image of a morphism `m` out of a
tensor product, on the pure tensor of two local sections, for a given lax structure. -/
noncomputable def tensoratorApp {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    [lax : (pushforwardModules h).LaxMonoidal]
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (V : Y.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj M)))
    (b : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj N))) :
    (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj P)) :=
  (Functor.LaxMonoidal.μ (pushforwardModules h) M N ≫ (pushforwardModules h).map m).val.app V
    ((PresheafOfModules.tensorSheafUnit (Osharp := Y.O) ((pushforwardModules h).obj M)
      ((pushforwardModules h).obj N)).app V (a ⊗ₜ b))

omit [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}] in
/-- `tensoratorApp` is the direct image of the morphism on the canonical pairing, for the lax
structure of Tag 03EL. -/
theorem tensoratorApp_eq {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (lax : (pushforwardModules h).LaxMonoidal)
    (hlax : lax = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal h)
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (V : Y.Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor Y.J V).obj (h.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)))
    (a : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj M)))
    (b : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules h).obj N)))
    (hz : (Sheaf.sectionsFunctor Y.J V).map (prodComparison h.toToposHom.pushforward
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) z =
        Functor.prodObjMk a b) :
    tensoratorApp h (lax := lax) m V a b =
      (Sheaf.sectionsFunctor Y.J V).map (h.toToposHom.pushforward.map
        (tensorPairing M N ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map m)) z := by
  subst hlax
  exact μ_comp_map_val_app_tensorSheafUnit h m V z a b hz

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The product comparisons of the direct images along `f` and along `(Sh(X), f⁻¹O_Y) ⟶ Y` of
the underlying sheaves of sets of `M` and of `M♭` agree. -/
theorem prodComparison_inverseImageRingedToposHom
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    prodComparison (inverseImageRingedToposHom f).toToposHom.pushforward
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)
        (restrictCoeffMod f M))
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)
        (restrictCoeffMod f N)) =
    prodComparison f.toToposHom.pushforward
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) :=
  rfl

omit [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The direct images along `f` and along `(Sh(X), f⁻¹O_Y) ⟶ Y` of a morphism of sheaves of
sets on `X` agree, read through any functor to types. -/
theorem map_pushforward_map_inverseImageRingedToposHom
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (Φ : Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)
          (restrictCoeffMod f M) ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)
          (restrictCoeffMod f N) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)
        (restrictCoeffMod f P))
    (S : Sheaf Y.J (Type w) ⥤ Type w)
    (z : S.obj (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))) :
    S.map (f.toToposHom.pushforward.map
        (show Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N ⟶
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P
        from Φ)) z = S.map ((inverseImageRingedToposHom f).toToposHom.pushforward.map Φ) z :=
  rfl

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- The pair of two local sections of the direct images along `f` is the pair of the same
sections of the direct images along `(Sh(X), f⁻¹O_Y) ⟶ Y`. -/
theorem prodObjMk_inverseImageRingedToposHom
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)))
    (y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N))) :
    Functor.prodObjMk (P := Sheaf.sectionsFunctor Y.J V) x y =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor Y.J V)
        (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules (inverseImageRingedToposHom f)).obj (restrictCoeffMod f M)))
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules (inverseImageRingedToposHom f)).obj (restrictCoeffMod f N))) x y :=
  rfl

/-- The `(Sh(X), f⁻¹O_Y) ⟶ Y` half of `tensoratorApp_chain`. -/
theorem map_pushforward_map_eq_tensoratorApp_inverseImageRingedToposHom
    (laxf : (pushforwardModules f).LaxMonoidal)
    (hf : laxf = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal f)
    (laxg : (pushforwardModules (inverseImageRingedToposHom f)).LaxMonoidal)
    (hg : laxg = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal
      (inverseImageRingedToposHom f))
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (m' : restrictCoeffMod f M ⊗ restrictCoeffMod f N ⟶ restrictCoeffMod f P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : (restrictCoeffMod f M).val.obj U)
        (b : (restrictCoeffMod f N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) (restrictCoeffMod f M)
          (restrictCoeffMod f N)).app U (a ⊗ₜ b)))
    (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)))
    (y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N)))
    (z : (Sheaf.sectionsFunctor Y.J V).obj (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)))
    (hz : (Sheaf.sectionsFunctor Y.J V).map (prodComparison
      f.toToposHom.pushforward (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) z =
          Functor.prodObjMk x y) :
    (Sheaf.sectionsFunctor Y.J V).map ((inverseImageRingedToposHom f).toToposHom.pushforward.map
        (tensorPairing (restrictCoeffMod f M) (restrictCoeffMod f N) ≫
          (Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)).map m')) z =
      tensoratorApp (inverseImageRingedToposHom f) (lax := laxg) m' V x y := by
  have hz'' := (congrArg (fun φ => (Sheaf.sectionsFunctor Y.J V).map φ z)
        (prodComparison_inverseImageRingedToposHom f M N)).trans
          (hz.trans (prodObjMk_inverseImageRingedToposHom f V x y))
  exact (tensoratorApp_eq (inverseImageRingedToposHom f) laxg hg m' V z x y hz'').symm

/-- The `f` half of `tensoratorApp_chain`: `tensoratorApp` along `f` is the direct image along
`(Sh(X), f⁻¹O_Y) ⟶ Y` of `m'` on the canonical pairing, at a section lifting the pair. -/
theorem tensoratorApp_eq_map_pushforward_map
    (laxf : (pushforwardModules f).LaxMonoidal)
    (hf : laxf = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal f)
    (laxg : (pushforwardModules (inverseImageRingedToposHom f)).LaxMonoidal)
    (hg : laxg = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal
      (inverseImageRingedToposHom f))
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (m' : restrictCoeffMod f M ⊗ restrictCoeffMod f N ⟶ restrictCoeffMod f P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : (restrictCoeffMod f M).val.obj U)
        (b : (restrictCoeffMod f N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) (restrictCoeffMod f M)
          (restrictCoeffMod f N)).app U (a ⊗ₜ b)))
    (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)))
    (y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N)))
    (z : (Sheaf.sectionsFunctor Y.J V).obj (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)))
    (hz : (Sheaf.sectionsFunctor Y.J V).map (prodComparison
      f.toToposHom.pushforward (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) z =
          Functor.prodObjMk x y) :
    tensoratorApp f (lax := laxf) m V x y =
      (Sheaf.sectionsFunctor Y.J V).map ((inverseImageRingedToposHom f).toToposHom.pushforward.map
        (tensorPairing (restrictCoeffMod f M) (restrictCoeffMod f N) ≫
          (Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)).map m')) z :=
  (tensoratorApp_eq f laxf hf m V z x y hz).trans
    ((congrArg (fun φ => (Sheaf.sectionsFunctor Y.J V).map (f.toToposHom.pushforward.map φ) z)
      (tensorPairing_comp_eq f m m' hm)).trans
    ((map_pushforward_map_inverseImageRingedToposHom f
      (tensorPairing (restrictCoeffMod f M) (restrictCoeffMod f N) ≫
        (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O)).map m')
      (Sheaf.sectionsFunctor Y.J V) z)))

/-- `μ_comp_map_val_app_eq_of_eq` at a given section of the direct image of the product
lifting the pair of sections. -/
theorem tensoratorApp_chain
    (laxf : (pushforwardModules f).LaxMonoidal)
    (hf : laxf = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal f)
    (laxg : (pushforwardModules (inverseImageRingedToposHom f)).LaxMonoidal)
    (hg : laxg = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal
      (inverseImageRingedToposHom f))
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (m' : restrictCoeffMod f M ⊗ restrictCoeffMod f N ⟶ restrictCoeffMod f P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : (restrictCoeffMod f M).val.obj U)
        (b : (restrictCoeffMod f N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) (restrictCoeffMod f M)
          (restrictCoeffMod f N)).app U (a ⊗ₜ b)))
    (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)))
    (y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N)))
    (z : (Sheaf.sectionsFunctor Y.J V).obj (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)))
    (hz : (Sheaf.sectionsFunctor Y.J V).map (prodComparison
      f.toToposHom.pushforward (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) z =
          Functor.prodObjMk x y) :
    tensoratorApp f (lax := laxf) m V x y =
      tensoratorApp (inverseImageRingedToposHom f) (lax := laxg) m' V x y :=
  (tensoratorApp_eq_map_pushforward_map f laxf hf laxg hg m m' hm V x y z hz).trans
    (map_pushforward_map_eq_tensoratorApp_inverseImageRingedToposHom f laxf hf laxg hg m m' hm
      V x y z hz)

/-- **The tensorator of the direct image along `f`, through the restriction of scalars to
`f⁻¹O_Y`, on pure tensors of local sections**: the tensorator of `f_*` followed by `f_*m` agrees
on pure tensors with the tensorator of the direct image along `(Sh(X), f⁻¹O_Y) ⟶ Y` followed by
the direct image of any `m'` agreeing with `m` on pure tensors; at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling, for any lax structures equal to the ones of
Tag 03EL. -/
theorem μ_comp_map_val_app_eq_of_eq
    (laxf : (pushforwardModules f).LaxMonoidal)
    (hf : laxf = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal f)
    (laxg : (pushforwardModules (inverseImageRingedToposHom f)).LaxMonoidal)
    (hg : laxg = Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal
      (inverseImageRingedToposHom f))
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (m : M ⊗ N ⟶ P)
    (m' : restrictCoeffMod f M ⊗ restrictCoeffMod f N ⟶ restrictCoeffMod f P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : (restrictCoeffMod f M).val.obj U)
        (b : (restrictCoeffMod f N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) (restrictCoeffMod f M)
          (restrictCoeffMod f N)).app U (a ⊗ₜ b)))
    (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)))
    (y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj N))) :
    tensoratorApp f (lax := laxf) m V x y =
      tensoratorApp (inverseImageRingedToposHom f) (lax := laxg) m' V x y := by
  have := f.toToposHom.adj.rightAdjoint_preservesLimits
  obtain ⟨z, hz⟩ : ∃ z, (Sheaf.sectionsFunctor Y.J V).map (prodComparison
      f.toToposHom.pushforward (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) z =
          Functor.prodObjMk x y :=
    ⟨_, ((Sheaf.sectionsFunctor Y.J V).map_comp_apply _ _ _).symm.trans
      ((congrArg (fun φ => (Sheaf.sectionsFunctor Y.J V).map φ (Functor.prodObjMk x y))
        (IsIso.inv_hom_id (prodComparison f.toToposHom.pushforward
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)))).trans
        ((Sheaf.sectionsFunctor Y.J V).map_id_apply _ _))⟩
  exact tensoratorApp_chain f laxf hf laxg hg m m' hm V x y z hz

end Key

section ToRingCat

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **The tensorator of the direct image along `f` through the restriction of scalars to
`f⁻¹O_Y`, on pure tensors of local sections**, at the `toRingCat` spelling the differential
graded transport is typed at: the tensorator of `f_*` followed by `f_*m` agrees on pure tensors
with the tensorator of the direct image along `(Sh(X), f⁻¹O_Y) ⟶ Y` followed by the direct image
of any `m'` agreeing with `m` on pure tensors. -/
theorem toposDirectImageModules_μ_comp_map_val_app
    {M N P : SheafOfModules.{w} (toRingCat X.J X.O)} (m : M ⊗ N ⟶ P)
    (m' : (restrictCoeffSheaf (coeffMap f)).obj M ⊗ (restrictCoeffSheaf (coeffMap f)).obj N ⟶
      (restrictCoeffSheaf (coeffMap f)).obj P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : ((restrictCoeffSheaf (coeffMap f)).obj M).val.obj U)
        (b : ((restrictCoeffSheaf (coeffMap f)).obj N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) ((restrictCoeffSheaf (coeffMap f)).obj M)
          ((restrictCoeffSheaf (coeffMap f)).obj N)).app U (a ⊗ₜ b)))
    (V : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((toposDirectImageModules f).obj M)))
    (y : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((toposDirectImageModules f).obj N))) :
    tensoratorApp f (lax := toposDirectImageModules_laxMonoidal f) m V x y =
      tensoratorApp (inverseImageRingedToposHom f)
        (lax := toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) m' V x y :=
  μ_comp_map_val_app_eq_of_eq f (toposDirectImageModules_laxMonoidal f) rfl
    (toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) rfl m m' hm V x y

/-- `tensoratorApp` along `f` at the `toRingCat` spelling, unfolded. -/
theorem tensoratorApp_toposDirectImageModules {M N P : SheafOfModules.{w} (toRingCat X.J X.O)}
    (m : M ⊗ N ⟶ P) (V : Y.Cᵒᵖ)
    (x : ((toposDirectImageModules f).obj M).val.obj V)
    (y : ((toposDirectImageModules f).obj N).val.obj V) :
    tensoratorApp f (lax := toposDirectImageModules_laxMonoidal f) m V x y =
      (Functor.LaxMonoidal.μ (toposDirectImageModules f) M N ≫
        (toposDirectImageModules f).map m).val.app V
      ((PresheafOfModules.tensorSheafUnit (Osharp := Y.O) ((toposDirectImageModules f).obj M)
        ((toposDirectImageModules f).obj N)).app V (x ⊗ₜ y)) := rfl

omit [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- `tensoratorApp` along `(Sh(X), f⁻¹O_Y) ⟶ Y` at the `toRingCat` spelling, unfolded. -/
theorem tensoratorApp_inverseImageRingedToposHom_toposDirectImageModules
    {M N P : SheafOfModules.{w} (toRingCat X.J X.O)}
    (m' : (restrictCoeffSheaf (coeffMap f)).obj M ⊗ (restrictCoeffSheaf (coeffMap f)).obj N ⟶
      (restrictCoeffSheaf (coeffMap f)).obj P) (V : Y.Cᵒᵖ)
    (x : ((toposDirectImageModules (inverseImageRingedToposHom f)).obj
      ((restrictCoeffSheaf (coeffMap f)).obj M)).val.obj V)
    (y : ((toposDirectImageModules (inverseImageRingedToposHom f)).obj
      ((restrictCoeffSheaf (coeffMap f)).obj N)).val.obj V) :
    tensoratorApp (inverseImageRingedToposHom f)
        (lax := toposDirectImageModules_laxMonoidal (inverseImageRingedToposHom f)) m' V x y =
    (Functor.LaxMonoidal.μ (toposDirectImageModules (inverseImageRingedToposHom f))
          ((restrictCoeffSheaf (coeffMap f)).obj M) ((restrictCoeffSheaf (coeffMap f)).obj N) ≫
        (toposDirectImageModules (inverseImageRingedToposHom f)).map m').val.app V
      ((PresheafOfModules.tensorSheafUnit (Osharp := Y.O)
        ((toposDirectImageModules (inverseImageRingedToposHom f)).obj
          ((restrictCoeffSheaf (coeffMap f)).obj M))
        ((toposDirectImageModules (inverseImageRingedToposHom f)).obj
          ((restrictCoeffSheaf (coeffMap f)).obj N))).app V (x ⊗ₜ y)) := rfl

/-- **The tensorator of the direct image along `f` through the restriction of scalars to
`f⁻¹O_Y`, on pure tensors of local sections**, unfolded at the `toRingCat` spelling: the
tensorator of `f_*` followed by `f_*m`, on the image of a pure tensor `x ⊗ y`, is the tensorator
of the direct image along `(Sh(X), f⁻¹O_Y) ⟶ Y` followed by the direct image of any `m'`
agreeing with `m` on pure tensors, on the image of the same pure tensor. -/
theorem toposDirectImageModules_μ_comp_map_app
    {M N P : SheafOfModules.{w} (toRingCat X.J X.O)} (m : M ⊗ N ⟶ P)
    (m' : (restrictCoeffSheaf (coeffMap f)).obj M ⊗ (restrictCoeffSheaf (coeffMap f)).obj N ⟶
      (restrictCoeffSheaf (coeffMap f)).obj P)
    (hm : ∀ (U : X.Cᵒᵖ) (a : ((restrictCoeffSheaf (coeffMap f)).obj M).val.obj U)
        (b : ((restrictCoeffSheaf (coeffMap f)).obj N).val.obj U),
      m.val.app U ((PresheafOfModules.tensorSheafUnit (Osharp := X.O) M N).app U
          ((show M.val.obj U from a) ⊗ₜ (show N.val.obj U from b))) =
        m'.val.app U ((PresheafOfModules.tensorSheafUnit
          (Osharp := inverseImageStructureSheaf f) ((restrictCoeffSheaf (coeffMap f)).obj M)
          ((restrictCoeffSheaf (coeffMap f)).obj N)).app U (a ⊗ₜ b)))
    (V : Y.Cᵒᵖ)
    (x : ((toposDirectImageModules f).obj M).val.obj V)
    (y : ((toposDirectImageModules f).obj N).val.obj V) :
    (Functor.LaxMonoidal.μ (toposDirectImageModules f) M N ≫
        (toposDirectImageModules f).map m).val.app V
      ((PresheafOfModules.tensorSheafUnit (Osharp := Y.O) ((toposDirectImageModules f).obj M)
        ((toposDirectImageModules f).obj N)).app V (x ⊗ₜ y)) =
    (Functor.LaxMonoidal.μ (toposDirectImageModules (inverseImageRingedToposHom f))
          ((restrictCoeffSheaf (coeffMap f)).obj M) ((restrictCoeffSheaf (coeffMap f)).obj N) ≫
        (toposDirectImageModules (inverseImageRingedToposHom f)).map m').val.app V
      ((PresheafOfModules.tensorSheafUnit (Osharp := Y.O)
        ((toposDirectImageModules (inverseImageRingedToposHom f)).obj
          ((restrictCoeffSheaf (coeffMap f)).obj M))
        ((toposDirectImageModules (inverseImageRingedToposHom f)).obj
          ((restrictCoeffSheaf (coeffMap f)).obj N))).app V (x ⊗ₜ y)) :=
  (tensoratorApp_toposDirectImageModules f m V x y).symm.trans
    ((toposDirectImageModules_μ_comp_map_val_app f m m' hm V x y).trans
      (tensoratorApp_inverseImageRingedToposHom_toposDirectImageModules f m' V x y))

end ToRingCat

end SheafOfModules.DifferentialGradedModule

end
