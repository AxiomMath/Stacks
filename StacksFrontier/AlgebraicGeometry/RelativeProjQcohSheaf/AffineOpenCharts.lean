module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RepresentableOfCharts

/-!
# Tag 01NV: `F_d` is representable

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN) and `d ≥ 1`.
[Stacks, Tag 01NV] says that the functor `F_d` of Section 01NS is representable by a scheme over
`S`, and the source proves it in four steps:

1. `F_d` is a sheaf on the big Zariski site;
2. `F_d` has a family of subfunctors which are representable by schemes, the charts;
3. those subfunctors cover `F_d`;
4. a Zariski sheaf covered by representable open subfunctors is representable.

Step (4) is Mathlib's [Stacks, Tag 01JJ]; step (1) is
`...RelativeProjQcohSheaf.Fd.isSheaf_functor`; and
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean` reduces the
tag to steps (2) and (3), the charts `c`, `hc`, `hcover`.

This file constructs those charts. They are indexed by the affine opens of `S`: for an affine
open `U` the chart is `...RelativeProjQcohSheaf.Fd.affineOpenChart`, the morphism of presheaves

`Mor(−, U_d(Γ(U, 𝒜))) ⟶ Shrink (F_d(−))`

into the canonical small model, where `U_d(Γ(U, 𝒜))` is the absolute degree-`d` open of
Equation 27.12.0.1 inside `Proj Γ(U, 𝒜)` — the scheme that [Stacks, Tag 01NU] over the affine
base `U` represents `F_d` of `𝒜|_U` by. The conclusion is
`...RelativeProjQcohSheaf.Fd.isRepresentable_functor_of_pos` and its form over the base
`...Fd.exists_representableBy_functor_of_pos`.

## Implementation notes

A chart is the composite of three bijections, each natural in the test scheme:

* `...RelativeProjQcohSheaf.Fd.chartEquiv` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartFdRepresentation.lean`, which is
  [Stacks, Tag 01NU] for the restricted algebra `𝒜|_U` on the affine scheme `U`, read at the
  graded ring `Γ(U, 𝒜)` the chart of `U` uses;
* `...RelativeProjQcohSheaf.Fd.restrictPullbackEquiv` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AlgebraTransport.lean`, which compares the
  **restriction** spelling `𝒜|_U` of the algebra with the **inverse image** spelling of
  [Stacks, Tag 01NT];
* `...RelativeProjQcohSheaf.Fd.baseFibreEquiv` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/BaseChangeFunctor.lean`, which is
  [Stacks, Tag 01NT]: `F_d` for the inverse image of `𝒜` along `U ⟶ S` is the fibre of `F_d` for
  `𝒜` over the morphisms into `U`.

Their composite `...RelativeProjQcohSheaf.Fd.chartUpEquiv` says that a morphism into the chart of
`U` is the same thing as a class of `F_d(T)` together with a factorization of its structure
morphism through `U`. That is exactly the statement that the chart is the **base change along
the structure morphism `F_d ⟶ h_S` of the open immersion `U ⟶ S`**, which is
`...RelativeProjQcohSheaf.Fd.isPullback_chartNat`, a pullback square of presheaves, and the two
properties the charts must have follow from it formally:

* `hc`, the relative representability of each chart by an open immersion, because
  `CategoryTheory.MorphismProperty.relative` is stable under base change and `U ⟶ S` is an open
  immersion;
* `hcover`, the joint local surjectivity, because the affine opens cover `S`, so a class in
  `F_d(T)` is in the image of the chart of `U` over the open `f⁻¹(U)` of `T`, `f` being its
  structure morphism, and those opens cover `T`.

Both are proved here for an arbitrary presheaf over `h_S` whose base changes to the members of
an open cover of `S` are given by pullback squares
(`...RelativeProjQcohSheaf.isOpenImmersion_presheaf_of_isPullback` and
`...RelativeProjQcohSheaf.isLocallySurjective_desc_of_isPullback`). The argument is the one of
`Stacks.RelativeSpecFunctorOfPoints.isRepresentable_of_representablePullbacks`, which concludes
representability from the same input but does not expose the charts.

## Main definitions

* `...RelativeProjQcohSheaf.Fd.smallToBase`: the projection of the canonical small model of `F_d`
  to `Hom(−, S)`.
* `...RelativeProjQcohSheaf.Fd.chartUp`: a class of `F_d` for `𝒜|_U` read as a class of `F_d` for
  `𝒜`, and `...Fd.chartUpEquiv`, the bijection onto the classes with a factorization through `U`.
* `...RelativeProjQcohSheaf.Fd.chartNat` and `...Fd.affineOpenChart`: **the chart of an affine
  open of the base**.

## Main results

* `...RelativeProjQcohSheaf.Fd.isPullback_chartNat`: **the chart of `U` is the base change of
  `U ⟶ S` along `F_d ⟶ h_S`**.
* `...RelativeProjQcohSheaf.Fd.isOpenImmersion_affineOpenChart` and
  `...Fd.isLocallySurjective_affineOpenCharts`: **the charts are relatively representable open
  immersions and are jointly surjective** — the source's steps (2) and (3).
* `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_pos` and
  `...Fd.isRepresentable_functor_of_pos`: **[Stacks, Tag 01NV]**.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}

/-! ### Charts out of a cover of the base -/

section FromCover

variable {F : Scheme.{u}ᵒᵖ ⥤ Type u} {π : F ⟶ yoneda.obj S}
  {𝒰 : S.OpenCover.{u}} {X : 𝒰.I₀ → Scheme.{u}}
  {c : (i : 𝒰.I₀) → yoneda.obj (X i) ⟶ F} {q : (i : 𝒰.I₀) → X i ⟶ 𝒰.X i}

/-- **A morphism of presheaves exhibited as the base change of a member of an open cover of the
base is a relatively representable open immersion.** This is `hc` of [Stacks, Tag 01JJ]'s input,
and the only thing it uses is that `CategoryTheory.MorphismProperty.relative` is stable under
base change. -/
theorem isOpenImmersion_presheaf_of_isPullback {i : 𝒰.I₀}
    (hpb : IsPullback (c i) (yoneda.map (q i)) π (yoneda.map (𝒰.f i))) :
    IsOpenImmersion.presheaf (c i) :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (P := @IsOpenImmersion)).of_isPullback hpb.flip
    (MorphismProperty.relative_map (𝒰.map_prop i))

/-- **A family of base changes of the members of an open cover of the base is jointly locally
surjective.** This is `hcover` of [Stacks, Tag 01JJ]'s input: a section over a test scheme `T`
has a morphism `f : T ⟶ S` under it, and over each member of the open cover of `T` that `f`
pulls back from the cover of `S` the section is in the image of the corresponding chart. -/
theorem isLocallySurjective_desc_of_isPullback
    (hpb : ∀ i, IsPullback (c i) (yoneda.map (q i)) π (yoneda.map (𝒰.f i))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c) := by
  constructor
  intro T p
  let f : T ⟶ S := π.app (op T) p
  let 𝒱 := 𝒰.pullback₁ f
  apply Scheme.zariskiTopology.superset_covering _ (Scheme.Cover.mem_grothendieckTopology 𝒱)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro V a ⟨i⟩
  let b : yoneda.obj (𝒱.X i) ⟶ F := yoneda.map (𝒱.f i) ≫ yonedaEquiv.symm p
  have hb0 : yoneda.map (pullback.snd f (𝒰.f i)) ≫ yoneda.map (𝒰.f i) = b ≫ π := by
    apply yonedaEquiv.injective
    change pullback.snd f (𝒰.f i) ≫ 𝒰.f i = π.app _ (F.map (𝒱.f i).op p)
    exact pullback.condition.symm.trans
      (ConcreteCategory.congr_hom (π.naturality (𝒱.f i).op) p).symm
  have hb : b ≫ π = yoneda.map (pullback.snd f (𝒰.f i)) ≫ yoneda.map (𝒰.f i) := hb0.symm
  let l : yoneda.obj (𝒱.X i) ⟶ yoneda.obj (X i) :=
    (hpb i).lift b (yoneda.map (pullback.snd f (𝒰.f i))) hb
  let m : 𝒱.X i ⟶ X i := yonedaEquiv l
  have hm : (c i).app (op (𝒱.X i)) m = F.map (𝒱.f i).op p :=
    congrArg yonedaEquiv ((hpb i).lift_fst b (yoneda.map (pullback.snd f (𝒰.f i))) hb)
  refine ⟨(Sigma.ι (fun i => yoneda.obj (X i)) i).app _ m, ?_⟩
  exact (ConcreteCategory.congr_hom
    (congrArg (fun α : _ ⟶ F => α.app (op (𝒱.X i))) (Sigma.ι_comp_desc c i)) m).trans hm

end FromCover

/-! ### The structure morphism on the canonical small model -/

section SmallToBase

variable (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)

/-- The projection of the canonical small model of `F_d` to the functor of points of `S`. -/
def Fd.smallToBase : Fd.smallPresheaf A d ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun (x : (Fd.smallPresheaf A d).obj T) =>
    (Fd.smallEquiv A d T.unop x).1
  naturality T T' φ := TypeCat.homEquiv.injective (funext fun x =>
    (congrArg (fun ξ : Fd A d T'.unop => ξ.1)
        (Fd.smallPresheaf_naturality A d φ.unop x)).trans
      (Fd.pullback_fst φ.unop (Fd.smallEquiv A d T.unop x)))

/-- The projection reads off the structure morphism of the class a section stands for. -/
@[simp] theorem Fd.smallToBase_app (T : Scheme.{u}ᵒᵖ) (x : (Fd.smallPresheaf A d).obj T) :
    (Fd.smallToBase A d).app T x = (Fd.smallEquiv A d T.unop x).1 := rfl

/-- The restriction maps of the small model, read on the classes. -/
theorem Fd.smallEquiv_map {T T' : Scheme.{u}ᵒᵖ} (ψ : T ⟶ T')
    (x : (Fd.smallPresheaf A d).obj T) :
    Fd.smallEquiv A d T'.unop ((Fd.smallPresheaf A d).map ψ x)
      = Fd.pullback ψ.unop (Fd.smallEquiv A d T.unop x) :=
  Fd.smallPresheaf_naturality A d ψ.unop x

/-- The restriction maps of the small model, read through the bijections in the other
direction. -/
theorem Fd.smallPresheaf_map_symm {T T' : Scheme.{u}} (ψ : T' ⟶ T) (ξ : Fd A d T) :
    (Fd.smallPresheaf A d).map ψ.op ((Fd.smallEquiv A d T).symm ξ)
      = (Fd.smallEquiv A d T').symm (Fd.pullback ψ ξ) := by
  apply (Fd.smallEquiv A d T').injective
  rw [Fd.smallPresheaf_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end SmallToBase

/-! ### `F_d` for the restriction of the algebra to an open of the base -/

section ChartUp

variable (A : SheafGradedAlgebra S) (U : S.Opens) (d : ℤ)

/-- The class of `F_d` for `𝒜` carried by a class of `F_d` for the restriction `𝒜|_U`. -/
def Fd.chartUp (T : Scheme.{u}) (ξ : Fd (situationAlgebra (A.restrict U.ι)) d T) :
    Fd (situationAlgebra A) d T :=
  Fd.baseChangeUp U.ι (situationAlgebra A) d (Fd.restrictPullbackEquiv A U.ι d T ξ)

/-- The structure morphism of the carried class is the one of the original, followed by the
inclusion of `U`. -/
@[simp] theorem Fd.chartUp_fst (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) d T) :
    (Fd.chartUp A U d T ξ).1 = ξ.1 ≫ U.ι := rfl

/-- Carrying a class up commutes with the pullback along a morphism of test schemes. -/
theorem Fd.chartUp_pullback {T T' : Scheme.{u}} (g : T' ⟶ T)
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) d T) :
    Fd.chartUp A U d T' (Fd.pullback g ξ) = Fd.pullback g (Fd.chartUp A U d T ξ) := by
  rw [Fd.chartUp, Fd.chartUp, Fd.restrictPullbackEquiv_pullback, Fd.baseChangeUp_pullback]

/-- **`F_d` for `𝒜|_U` is the fibre of `F_d` for `𝒜` over the morphisms into `U`.** -/
def Fd.chartUpEquiv (T : Scheme.{u}) :
    Fd (situationAlgebra (A.restrict U.ι)) d T ≃
      {p : ULift.{u + 1, u} (T ⟶ U.toScheme) × Fd (situationAlgebra A) d T //
        p.1.down ≫ U.ι = p.2.1} :=
  (Fd.restrictPullbackEquiv A U.ι d T).trans
    (Fd.baseFibreEquiv U.ι (situationAlgebra A) d T)

/-- The bijection sends a class to its structure morphism together with the class it carries. -/
@[simp] theorem Fd.chartUpEquiv_apply (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) d T) :
    (Fd.chartUpEquiv A U d T ξ).1 = (ULift.up ξ.1, Fd.chartUp A U d T ξ) := rfl

end ChartUp

/-! ### The chart of an affine open of the base -/

section Chart

variable (A : SheafGradedAlgebra S) (U : S.Opens) (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k)

/-- The morphism from the chart of `U` to `U`. -/
def Fd.chartBaseHom : (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme ⟶ U.toScheme :=
  ((Fd.chartEquiv A U hU hk
    (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme).symm (𝟙 _)).1

/-- The inverse of `Fd.chartEquiv` turns precomposition into pullback. -/
private theorem Fd.chartEquiv_symm_comp {T T' : Scheme.{u}} (g : T' ⟶ T)
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme) :
    (Fd.chartEquiv A U hU hk T').symm (g ≫ φ)
      = Fd.pullback g ((Fd.chartEquiv A U hU hk T).symm φ) := by
  apply (Fd.chartEquiv A U hU hk T').injective
  rw [Equiv.apply_symm_apply, Fd.chartEquiv_pullback, Equiv.apply_symm_apply]

/-- The structure morphism of the class a morphism into the chart of `U` stands for is that
morphism followed by `Fd.chartBaseHom`. This is the naturality of `Fd.chartEquiv` read at the
identity of the chart. -/
theorem Fd.chartEquiv_symm_fst {T : Scheme.{u}}
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme) :
    ((Fd.chartEquiv A U hU hk T).symm φ).1 = φ ≫ Fd.chartBaseHom A U hU hk := by
  have key := Fd.chartEquiv_symm_comp A U hU hk φ (𝟙 _)
  rw [Category.comp_id] at key
  rw [key, Fd.pullback_fst]
  rfl

/-- The class of `F_d` for `𝒜` that a morphism into the chart of `U` defines. -/
def Fd.chartOfHom (T : Scheme.{u})
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme) :
    Fd (situationAlgebra A) (k : ℤ) T :=
  Fd.chartUp A U (k : ℤ) T ((Fd.chartEquiv A U hU hk T).symm φ)

/-- The class attached to a morphism into the chart of `U` has a structure morphism that
factors through `U`. -/
theorem Fd.chartOfHom_fst (T : Scheme.{u})
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme) :
    (Fd.chartOfHom A U hU hk T φ).1 = (φ ≫ Fd.chartBaseHom A U hU hk) ≫ U.ι := by
  rw [Fd.chartOfHom, Fd.chartUp_fst, Fd.chartEquiv_symm_fst]

/-- The class attached to a morphism into the chart of `U` is natural in the test scheme. -/
theorem Fd.chartOfHom_pullback {T T' : Scheme.{u}} (g : T' ⟶ T)
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme) :
    Fd.chartOfHom A U hU hk T' (g ≫ φ)
      = Fd.pullback g (Fd.chartOfHom A U hU hk T φ) := by
  rw [Fd.chartOfHom, Fd.chartOfHom, ← Fd.chartUp_pullback, Fd.chartEquiv_symm_comp]

/-- The morphism into the chart of `U` attached to a class of `F_d` for `𝒜` whose structure
morphism is given a factorization through `U`. -/
def Fd.chartHomOfFibre (T : Scheme.{u}) (a : T ⟶ U.toScheme)
    (ξ : Fd (situationAlgebra A) (k : ℤ) T) (h : a ≫ U.ι = ξ.1) :
    T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme :=
  Fd.chartEquiv A U hU hk T ((Fd.chartUpEquiv A U (k : ℤ) T).symm ⟨(ULift.up a, ξ), h⟩)

/-- The two components of a pair read back through `Fd.chartUpEquiv`. -/
private theorem Fd.chartUpEquiv_symm_components (T : Scheme.{u}) (a : T ⟶ U.toScheme)
    (ξ : Fd (situationAlgebra A) (k : ℤ) T) (h : a ≫ U.ι = ξ.1) :
    (ULift.up.{u + 1, u} a, ξ)
      = (ULift.up ((Fd.chartUpEquiv A U (k : ℤ) T).symm ⟨(ULift.up a, ξ), h⟩).1,
          Fd.chartUp A U (k : ℤ) T ((Fd.chartUpEquiv A U (k : ℤ) T).symm
            ⟨(ULift.up a, ξ), h⟩)) := by
  have e := Fd.chartUpEquiv_apply A U (k : ℤ) T
    ((Fd.chartUpEquiv A U (k : ℤ) T).symm ⟨(ULift.up a, ξ), h⟩)
  rw [Equiv.apply_symm_apply] at e
  exact e

/-- The morphism into the chart attached to a class stands for that class. -/
@[simp] theorem Fd.chartOfHom_chartHomOfFibre (T : Scheme.{u}) (a : T ⟶ U.toScheme)
    (ξ : Fd (situationAlgebra A) (k : ℤ) T) (h : a ≫ U.ι = ξ.1) :
    Fd.chartOfHom A U hU hk T (Fd.chartHomOfFibre A U hU hk T a ξ h) = ξ := by
  rw [Fd.chartOfHom, Fd.chartHomOfFibre, Equiv.symm_apply_apply]
  exact (congrArg Prod.snd (Fd.chartUpEquiv_symm_components A U T a ξ h)).symm

/-- The morphism into the chart attached to a class lies over the given factorization. -/
@[simp] theorem Fd.chartHomOfFibre_comp_chartBaseHom (T : Scheme.{u}) (a : T ⟶ U.toScheme)
    (ξ : Fd (situationAlgebra A) (k : ℤ) T) (h : a ≫ U.ι = ξ.1) :
    Fd.chartHomOfFibre A U hU hk T a ξ h ≫ Fd.chartBaseHom A U hU hk = a := by
  rw [← Fd.chartEquiv_symm_fst, Fd.chartHomOfFibre, Equiv.symm_apply_apply]
  exact (congrArg ULift.down (congrArg Prod.fst
    (Fd.chartUpEquiv_symm_components A U T a ξ h))).symm

/-- **A morphism into the chart of `U` is determined by the class it stands for and the
factorization it lies over.** -/
theorem Fd.eq_chartHomOfFibre (T : Scheme.{u}) (a : T ⟶ U.toScheme)
    (ξ : Fd (situationAlgebra A) (k : ℤ) T) (h : a ≫ U.ι = ξ.1)
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme)
    (h₁ : Fd.chartOfHom A U hU hk T φ = ξ)
    (h₂ : φ ≫ Fd.chartBaseHom A U hU hk = a) :
    φ = Fd.chartHomOfFibre A U hU hk T a ξ h := by
  have key : (Fd.chartEquiv A U hU hk T).symm φ
      = (Fd.chartUpEquiv A U (k : ℤ) T).symm ⟨(ULift.up a, ξ), h⟩ := by
    apply (Fd.chartUpEquiv A U (k : ℤ) T).injective
    rw [Equiv.apply_symm_apply]
    refine Subtype.ext ((Fd.chartUpEquiv_apply A U (k : ℤ) T _).trans (Prod.ext ?_ ?_))
    · exact congrArg ULift.up ((Fd.chartEquiv_symm_fst A U hU hk φ).trans h₂)
    · exact h₁
  exact ((Equiv.apply_symm_apply (Fd.chartEquiv A U hU hk T) φ).symm.trans
    (congrArg (Fd.chartEquiv A U hU hk T) key))

/-! ### The chart as a morphism of presheaves -/

/-- **The chart of an affine open `U` of the base**: the morphism of presheaves from the functor
of points of the absolute degree-`d` open of `Γ(U, 𝒜)` to the canonical small model of `F_d`. -/
def Fd.chartNat :
    yoneda.obj (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme ⟶
      Fd.smallPresheaf (situationAlgebra A) (k : ℤ) where
  app T := TypeCat.ofHom fun (φ : (yoneda.obj
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme).obj T) =>
    (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop).symm
      (Fd.chartOfHom A U hU hk T.unop φ)
  naturality T T' ψ := TypeCat.homEquiv.injective (funext fun φ =>
    (congrArg (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T'.unop).symm
        (Fd.chartOfHom_pullback A U hU hk ψ.unop φ)).trans
      (Fd.smallPresheaf_map_symm (situationAlgebra A) (k : ℤ) ψ.unop
        (Fd.chartOfHom A U hU hk T.unop φ)).symm)

/-- The chart sends a morphism into the degree-`d` open to the class it stands for. -/
@[simp] theorem Fd.chartNat_app (T : Scheme.{u}ᵒᵖ)
    (φ : (yoneda.obj
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme).obj T) :
    (Fd.chartNat A U hU hk).app T φ
      = (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop).symm
          (Fd.chartOfHom A U hU hk T.unop φ) := rfl

/-- The chart of `U` lies over the inclusion of `U` into `S`. -/
theorem Fd.chartNat_comp_smallToBase :
    Fd.chartNat A U hU hk ≫ Fd.smallToBase (situationAlgebra A) (k : ℤ)
      = yoneda.map (Fd.chartBaseHom A U hU hk) ≫ yoneda.map U.ι :=
  NatTrans.ext (funext fun T => TypeCat.homEquiv.injective (funext fun φ => by
    change (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop
        ((Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop).symm
          (Fd.chartOfHom A U hU hk T.unop φ))).1 = _
    rw [Equiv.apply_symm_apply, Fd.chartOfHom_fst]
    rfl))

end Chart

/-! ### The chart is the base change of the open of the base -/

section ChartPullback

variable (A : SheafGradedAlgebra S) (U : S.Opens) (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k)

section Cone

variable (s : PullbackCone (Fd.smallToBase (situationAlgebra A) (k : ℤ)) (yoneda.map U.ι))

/-- The factorization through `U` that a cone over the cospan provides. -/
theorem Fd.chartCone_cond (T : Scheme.{u}ᵒᵖ) (w : s.pt.obj T) :
    s.snd.app T w ≫ U.ι
      = (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop (s.fst.app T w)).1 :=
  (ConcreteCategory.congr_hom
    (congrArg (fun α : s.pt ⟶ yoneda.obj S => α.app T) s.condition) w).symm

/-- The morphism into the chart of `U` that a cone over the cospan determines. -/
def Fd.chartLift :
    s.pt ⟶ yoneda.obj (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme where
  app T := TypeCat.ofHom fun w => Fd.chartHomOfFibre A U hU hk T.unop (s.snd.app T w)
    (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop (s.fst.app T w))
    (Fd.chartCone_cond A U s T w)
  naturality T T' ψ := TypeCat.homEquiv.injective (funext fun w => by
    refine (Fd.eq_chartHomOfFibre A U hU hk T'.unop _ _ (Fd.chartCone_cond A U s T' _)
      (ψ.unop ≫ Fd.chartHomOfFibre A U hU hk T.unop (s.snd.app T w)
        (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop (s.fst.app T w))
        (Fd.chartCone_cond A U s T w)) ?_ ?_).symm
    · rw [Fd.chartOfHom_pullback, Fd.chartOfHom_chartHomOfFibre]
      exact ((congrArg (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T'.unop)
          (NatTrans.naturality_apply s.fst ψ w)).trans
        (Fd.smallEquiv_map (situationAlgebra A) (k : ℤ) ψ (s.fst.app T w))).symm
    · rw [Category.assoc, Fd.chartHomOfFibre_comp_chartBaseHom]
      exact (NatTrans.naturality_apply s.snd ψ w).symm)

/-- The lift on an element of the vertex of the cone. -/
@[simp] theorem Fd.chartLift_app (T : Scheme.{u}ᵒᵖ) (w : s.pt.obj T) :
    (Fd.chartLift A U hU hk s).app T w
      = Fd.chartHomOfFibre A U hU hk T.unop (s.snd.app T w)
          (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop (s.fst.app T w))
          (Fd.chartCone_cond A U s T w) := rfl

/-- The lift is compatible with the chart. -/
theorem Fd.chartLift_comp_chartNat :
    Fd.chartLift A U hU hk s ≫ Fd.chartNat A U hU hk = s.fst :=
  NatTrans.ext (funext fun T => TypeCat.homEquiv.injective (funext fun w => by
    change (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop).symm
        (Fd.chartOfHom A U hU hk T.unop ((Fd.chartLift A U hU hk s).app T w)) = _
    rw [Fd.chartLift_app, Fd.chartOfHom_chartHomOfFibre, Equiv.symm_apply_apply]
    rfl))

/-- The lift is compatible with the projection to `U`. -/
theorem Fd.chartLift_comp_chartBaseHom :
    Fd.chartLift A U hU hk s ≫ yoneda.map (Fd.chartBaseHom A U hU hk) = s.snd :=
  NatTrans.ext (funext fun T => TypeCat.homEquiv.injective (funext fun w => by
    change (Fd.chartLift A U hU hk s).app T w ≫ Fd.chartBaseHom A U hU hk = _
    rw [Fd.chartLift_app, Fd.chartHomOfFibre_comp_chartBaseHom]
    rfl))

/-- The lift is the only morphism compatible with both projections. -/
theorem Fd.eq_chartLift
    (m : s.pt ⟶ yoneda.obj (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme)
    (h₁ : m ≫ Fd.chartNat A U hU hk = s.fst)
    (h₂ : m ≫ yoneda.map (Fd.chartBaseHom A U hU hk) = s.snd) :
    m = Fd.chartLift A U hU hk s := by
  refine NatTrans.ext (funext fun T => TypeCat.homEquiv.injective (funext fun w => ?_))
  have h₁' := ConcreteCategory.congr_hom (NatTrans.congr_app h₁ T) w
  have h₂' := ConcreteCategory.congr_hom (NatTrans.congr_app h₂ T) w
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Fd.chartNat_app,
    yoneda_map_app] at h₁' h₂'
  have hA : Fd.chartOfHom A U hU hk T.unop (m.app T w)
      = Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop (s.fst.app T w) := by
    rw [← h₁', Equiv.apply_symm_apply]
  change m.app T w = (Fd.chartLift A U hU hk s).app T w
  rw [Fd.chartLift_app]
  exact Fd.eq_chartHomOfFibre A U hU hk T.unop (s.snd.app T w)
    (Fd.smallEquiv (situationAlgebra A) (k : ℤ) T.unop (s.fst.app T w))
    (Fd.chartCone_cond A U s T w) (m.app T w) hA h₂'

end Cone

/-- **The chart of an affine open `U` of the base is the base change of `U ⊆ S` along the
structure morphism of `F_d`.** -/
theorem Fd.isPullback_chartNat :
    IsPullback (Fd.chartNat A U hU hk) (yoneda.map (Fd.chartBaseHom A U hU hk))
      (Fd.smallToBase (situationAlgebra A) (k : ℤ)) (yoneda.map U.ι) :=
  IsPullback.of_isLimit' ⟨Fd.chartNat_comp_smallToBase A U hU hk⟩
    (PullbackCone.IsLimit.mk _ (fun s => Fd.chartLift A U hU hk s)
      (fun s => Fd.chartLift_comp_chartNat A U hU hk s)
      (fun s => Fd.chartLift_comp_chartBaseHom A U hU hk s)
      (fun s m h₁ h₂ => Fd.eq_chartLift A U hU hk s m h₁ h₂))

end ChartPullback

/-! ### Tag 01NV -/

section Assembly

variable (A : SheafGradedAlgebra S) {k : ℕ} (hk : 0 < k)

/-- **The chart of `F_d` attached to an affine open of the base.** -/
def Fd.affineOpenChart (V : S.affineOpens) :
    yoneda.obj (AlgebraicGeometry.Proj.degreeOpen (A.grading V.1) k).toScheme ⟶
      Fd.smallPresheaf (situationAlgebra A) (k : ℤ) :=
  Fd.chartNat A V.1 V.2 hk

/-- Each chart is a relatively representable open immersion. -/
theorem Fd.isOpenImmersion_affineOpenChart (V : S.affineOpens) :
    IsOpenImmersion.presheaf (Fd.affineOpenChart A hk V) :=
  isOpenImmersion_presheaf_of_isPullback
    (π := Fd.smallToBase (situationAlgebra A) (k : ℤ)) (𝒰 := S.directedAffineCover)
    (c := fun W : S.affineOpens => Fd.affineOpenChart A hk W)
    (q := fun W : S.affineOpens => Fd.chartBaseHom A W.1 W.2 hk)
    (Fd.isPullback_chartNat A V.1 V.2 hk)

/-- The charts are jointly surjective. -/
theorem Fd.isLocallySurjective_affineOpenCharts :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun V : S.affineOpens => Fd.affineOpenChart A hk V) :=
  isLocallySurjective_desc_of_isPullback
    (π := Fd.smallToBase (situationAlgebra A) (k : ℤ)) (𝒰 := S.directedAffineCover)
    (c := fun W : S.affineOpens => Fd.affineOpenChart A hk W)
    (q := fun W : S.affineOpens => Fd.chartBaseHom A W.1 W.2 hk)
    (fun V => Fd.isPullback_chartNat A V.1 V.2 hk)

include hk in
/-- **Stacks Project, Tag 01NV.** Let `S` be a scheme, `𝒜` a quasi-coherent graded
`𝒪_S`-algebra (Situation 01NN) and `d ≥ 1`. The functor `F_d` of Section 01NS is representable
by a scheme over `S`: there are a scheme `Y`, a morphism `p : Y ⟶ S` and a representation of
`F_d` by `Y` under which the morphism `T ⟶ Y` representing a class `ξ ∈ F_d(T)`, composed with
`p`, is the morphism `T ⟶ S` recorded by `ξ`. -/
@[stacks 01NV "THE TAG, UNCONDITIONALLY: for S a scheme, A a quasi-coherent graded O_S-algebra \
(Situation 01NN) and d = k with 0 < k, the functor F_d of Section 01NS is representable by \
a scheme over S. The conclusion is about Fd.functor, the genuine functor whose restriction maps \
are the pullback of a quadruple, and it records that the representing morphism composed with \
p : Y -> S is the class's own morphism to S."]
theorem Fd.exists_representableBy_functor_of_pos :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S)
      (e : (Fd.functor (situationAlgebra A) (k : ℤ)).RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : Fd (situationAlgebra A) (k : ℤ) T),
        e.homEquiv.symm ξ ≫ p = ξ.1 :=
  Fd.exists_representableBy_functor_of_charts' (situationAlgebra A) (k : ℤ)
    (fun V : S.affineOpens => Fd.affineOpenChart A hk V)
    (fun V => Fd.isOpenImmersion_affineOpenChart A hk V)
    (Fd.isLocallySurjective_affineOpenCharts A hk)

include hk in
/-- **Stacks Project, Tag 01NV, in the bare form.** This is
`Fd.exists_representableBy_functor_of_pos` forgetting the structure morphism to `S`. -/
theorem Fd.isRepresentable_functor_of_pos :
    (Fd.functor (situationAlgebra A) (k : ℤ)).IsRepresentable :=
  Fd.isRepresentable_functor_of_charts' (situationAlgebra A) (k : ℤ)
    (fun V : S.affineOpens => Fd.affineOpenChart A hk V)
    (fun V => Fd.isOpenImmersion_affineOpenChart A hk V)
    (Fd.isLocallySurjective_affineOpenCharts A hk)

end Assembly

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
