module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFibreSections
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineBasePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange

/-!
# The relative-dimension bound descends in the fibred category of proper flat families

`AlgebraicGeometry.DescendsRelativeDimensionLEOne` is the one geometric statement the source's
proof of **Stacks 0D55** reduces to: along an affine cofiltered inverse limit in the big fppf
site of `Spec(ℤ)`, if a finitely presented flat proper family over a stage has base change to
the vertex of relative dimension at most one, then its base change to some later stage already
has. It is **Stacks 0D4K** read in the category
`AlgebraicGeometry.CartesianProperFlatSpaces`.

This file discharges it. The statement about families is turned into a statement about base
changes of structure morphisms of algebraic spaces, and that statement is then the affine-base,
size-free form of Stacks 0D4K which the library proves,
`AlgebraicGeometry.Space.exists_hasRelativeDimensionLE_isPullback_of_limit`.

## Main definitions

* `AlgebraicGeometry.DescendsRelativeDimensionAlongAffineLimit`: the relative-dimension bound
  descends along an affine cofiltered limit, stated on base changes of structure morphisms of
  algebraic spaces rather than on morphisms of the fibred category. This is the shape in which
  the geometric content is available.

## Main results

* `AlgebraicGeometry.descendsRelativeDimensionLEOne_of_descendsAlongAffineLimit`: the descent
  clause for the fibred category follows from the one for base changes of structure morphisms.
* `AlgebraicGeometry.descendsRelativeDimensionAlongAffineLimit_one`: the latter holds, at index
  universes equal to the universe of the schemes.
* `AlgebraicGeometry.descendsRelativeDimensionLEOne`: **Stacks 0D4K in the fibred category of
  finitely presented flat proper families**, with no hypothesis — the input the reduction of
  Stacks 0D55 in `StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreserving` asks for.

## Implementation notes

*The two bridges between the fibred category and the algebraic spaces.* A morphism of
`AlgebraicGeometry.CartesianProperFlatSpaces` lying over a morphism of the base is a cartesian
square of structure morphisms; that is Stacks 04U9 on these families, and it is
`AlgebraicGeometry.ProperFlatFibre.isPullback_map`. It turns the given morphism `ε` of families
into the cartesian square the geometric statement consumes. Conversely the projection is fibred
in groupoids (`AlgebraicGeometry.cartesianProperFlatProjection_isFiberedInGroupoids`), so the
transition morphism of the inverse system lifts to a morphism of families into the given one;
finite presentation, flatness and properness survive because the lift is cartesian
(`AlgebraicGeometry.closedUnderStronglyCartesian_isProperFlatSpace`), and the structure
morphism of the lift is again a base change of the given one, so the bound the geometric
statement returns transfers to it: two cartesian squares over the same morphism with the same
target are isomorphic, and the relative-dimension bound is invariant under an isomorphism of
the morphism.

*The `eqToHom` of the fibre.* An object of the fibre of the projection over `U` is a family
together with a *proof* that its base is `U`, so its structure morphism read over `U`
(`AlgebraicGeometry.ProperFlatFibre.str`) is the structure morphism it carries in the comma
category composed with the Yoneda image of that identification. The bound, local finiteness of
type and quasi-compactness therefore have to be moved across an isomorphism of representables;
`AlgebraicGeometry.Space.hasRelativeDimensionLE_of_iso` and
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_iso` are the two transfers, both read off a
square with two invertible vertical edges, which is cartesian.

*Index universes.* The geometric input is proved for an index category `I : Type u` with
`Category.{u} I`, `u` the universe of the schemes, so
`AlgebraicGeometry.descendsRelativeDimensionLEOne` is stated at
`DescendsRelativeDimensionLEOne.{u, u, u}`. That is the library's convention for a Stacks 07XL
condition — the inverse systems of Stacks 07XL are directed sets, which are small — and is the
form in which Stacks 0D43 is proved as
`AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`.

No Stacks tag attribute is placed: Stacks 0D4K is already registered, in the index-bounded
setting, on `exists_hasRelativeDimensionLE_mapAt` in the namespace
`AlgebraicGeometry.Space.ChartData.MorphismDescentSystemOfChartsBounded`.

## References

* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

/-- **The relative-dimension bound descends along an affine cofiltered limit, on base changes of
structure morphisms.** Let `T = lim Tᵢ` be an affine cofiltered inverse limit in the big fppf
site of `S`, let `fi : Xi ⟶ Tᵢ` be a quasi-compact algebraic space over a stage, locally of
finite type, and let `fT : XT ⟶ T` be its base change to the vertex, presented by any cartesian
square over the cone leg. If `fT` has relative dimension at most `d`, then the base change of
`fi` to some later stage already has.

This is the affine-base, size-free form of **Stacks 0D4K**: the index category carries no
cardinality hypothesis. -/
def DescendsRelativeDimensionAlongAffineLimit (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I) (Xi XT : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fi : Xi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (fT : XT ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt))
      (g : XT ⟶ Xi),
      IsAlgebraicSpace B S hS Xi →
      Space.IsQuasiCompactSpace B S hS Xi →
      IsPullback fT g
          (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi →
      Space.IsLocallyOfFiniteType B S hS fi →
      Space.HasRelativeDimensionLE d B S hS fT →
      ∃ (k : I) (s : k ⟶ i) (Xk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (fk : Xk ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
        (hk : Xk ⟶ Xi),
        IsPullback fk hk
            (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi ∧
          Space.HasRelativeDimensionLE d B S hS fk

section Transfer

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative-dimension bound is invariant under an isomorphism of the morphism.** A square
whose two vertical edges are invertible is cartesian, so this is Stacks 04NS. -/
theorem Space.hasRelativeDimensionLE_of_iso {d : ℕ}
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (ea : X ≅ X') (eb : Y ≅ Y') (hsq : f ≫ eb.hom = ea.hom ≫ f')
    (hX' : IsAlgebraicSpace B S hS X') (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y')
    (hf' : Space.IsLocallyOfFiniteType B S hS f')
    (hf : Space.HasRelativeDimensionLE d B S hS f) :
    Space.HasRelativeDimensionLE d B S hS f' := by
  have sq : IsPullback f ea.hom eb.hom f' := IsPullback.of_vert_isIso ⟨hsq⟩
  intro x'
  obtain ⟨x, rfl⟩ := (Space.bijective_pointsMap_of_isIso B S hS ea.hom).2 x'
  obtain ⟨e, he, hrel⟩ := hf x
  exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS (e : ℕ∞) sq
    hX' hY' hY hf' x).mp hrel⟩

/-- **Being locally of finite type is invariant under an isomorphism of the morphism.** The
chart condition of Stacks 03MJ respects isomorphisms of presheaves. -/
theorem Space.isLocallyOfFiniteType_of_iso
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (ea : X ≅ X') (eb : Y ≅ Y') (hsq : f ≫ eb.hom = ea.hom ≫ f')
    (hf : Space.IsLocallyOfFiniteType B S hS f) :
    Space.IsLocallyOfFiniteType B S hS f' := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.IsLocallyOfFiniteType B S hS g
  have _ : P.RespectsIso := Space.isLocallyOfFiniteType_respectsIso B S hS
  have hfe : f' = ea.inv ≫ f ≫ eb.hom := by
    rw [hsq]
    simp
  change P f'
  rw [hfe, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact hf

end Transfer

namespace ProperFlatFibre

section Fibre

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local implicit_reducible] Functor.Fiber

/-- The structure morphism of an object of the fibre over `U`, read over `U`, is the structure
morphism it carries in the comma category followed by the identification of its base with
`U`. -/
theorem str_def (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    ProperFlatFibre.str x = x.val.obj.obj.hom ≫ yoneda.map (eqToHom x.property) := rfl

/-- The identification of the base of an object of the fibre with the index of the fibre, read
as an isomorphism of representable presheaves. -/
abbrev baseIso (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    yoneda.obj x.val.obj.obj.right ≅ yoneda.obj U :=
  yoneda.mapIso (eqToIso x.property)

/-- The square identifying the structure morphism an object of the fibre carries in the comma
category with the one it carries over the index of the fibre. -/
theorem str_sq (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    x.val.obj.obj.hom ≫ (baseIso B S hS U x).hom =
      (Iso.refl (ProperFlatFibre.space x)).hom ≫ ProperFlatFibre.str x := by
  refine Eq.trans ?_ (Category.id_comp _).symm
  rw [str_def]
  rfl

/-- The same square, read in the other direction. -/
theorem str_sq' (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    ProperFlatFibre.str x ≫ (baseIso B S hS U x).symm.hom =
      (Iso.refl (ProperFlatFibre.space x)).hom ≫ x.val.obj.obj.hom := by
  rw [Iso.symm_hom, Iso.comp_inv_eq]
  exact (str_sq B S hS U x).symm.trans (by simp)

/-- The structure morphism an object of the fibre carries in the comma category is locally of
finite type, being of finite presentation. -/
theorem isLocallyOfFiniteType_hom (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    Space.IsLocallyOfFiniteType B S hS x.val.obj.obj.hom :=
  Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    x.val.obj.property.1.1

/-- Being locally of finite type passes to the structure morphism read over the index of the
fibre. -/
theorem isLocallyOfFiniteType_str (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    Space.IsLocallyOfFiniteType B S hS (ProperFlatFibre.str x) :=
  Space.isLocallyOfFiniteType_of_iso B S hS (Iso.refl _) (baseIso B S hS U x)
    (str_sq B S hS U x) (isLocallyOfFiniteType_hom B S hS U x)

/-- **The algebraic space carrying an object of the fibre over a quasi-compact base is
quasi-compact**, its structure morphism being of finite presentation. -/
theorem isQuasiCompactSpace_space (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U)
    (hU : Space.IsQuasiCompactSpace B S hS (yoneda.obj U)) :
    Space.IsQuasiCompactSpace B S hS (ProperFlatFibre.space x) := by
  have hU' : Space.IsQuasiCompactSpace B S hS (yoneda.obj x.val.obj.obj.right) := by
    rw [show x.val.obj.obj.right = U from x.property]
    exact hU
  exact Space.isQuasiCompactSpace_of_isFinitePresentation B S hS x.val.obj.obj.hom
    (isAlgebraicSpace_yoneda B S hS x.val.obj.obj.right) hU' x.val.obj.property.1

/-- The relative-dimension bound passes to the structure morphism read over the index of the
fibre. -/
theorem hasRelativeDimensionLE_str (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (d : ℕ)
    (hx : Space.HasRelativeDimensionLE d B S hS x.val.obj.obj.hom) :
    Space.HasRelativeDimensionLE d B S hS (ProperFlatFibre.str x) :=
  Space.hasRelativeDimensionLE_of_iso B S hS (Iso.refl _) (baseIso B S hS U x)
    (str_sq B S hS U x) (ProperFlatFibre.isAlgebraicSpace_space x)
    (isAlgebraicSpace_yoneda B S hS x.val.obj.obj.right)
    (isAlgebraicSpace_yoneda B S hS U) (isLocallyOfFiniteType_str B S hS U x) hx

/-- The relative-dimension bound passes back from the structure morphism read over the index of
the fibre to the one carried in the comma category. -/
theorem hasRelativeDimensionLE_of_str (U : BigFppfOver B S hS)
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (d : ℕ)
    (hx : Space.HasRelativeDimensionLE d B S hS (ProperFlatFibre.str x)) :
    Space.HasRelativeDimensionLE d B S hS x.val.obj.obj.hom :=
  Space.hasRelativeDimensionLE_of_iso B S hS (Iso.refl _) (baseIso B S hS U x).symm
    (str_sq' B S hS U x) (ProperFlatFibre.isAlgebraicSpace_space x)
    (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_yoneda B S hS x.val.obj.obj.right)
    (isLocallyOfFiniteType_hom B S hS U x) hx

end Fibre

end ProperFlatFibre

section Descent

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

attribute [local implicit_reducible] Functor.Fiber

/-- **Stacks 0D4K in the fibred category of finitely presented flat proper families, from its
form on base changes of structure morphisms.** -/
theorem descendsRelativeDimensionLEOne_of_descendsAlongAffineLimit
    (h : DescendsRelativeDimensionAlongAffineLimit.{u, v, w} B integerBase hZ 1) :
    DescendsRelativeDimensionLEOne.{u, v, w} B hZ := by
  intro I _ _ D c hc i Zi ZT ε hε hdim
  have := hε
  let xT : (cartesianProperFlatProjection B integerBase hZ).Fiber
      ((BigAffineFppf.inclusion B integerBase hZ).obj c.pt) :=
    ⟨ZT, IsHomLift.domain_eq (cartesianProperFlatProjection B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ε⟩
  let xi : (cartesianProperFlatProjection B integerBase hZ).Fiber
      ((BigAffineFppf.inclusion B integerBase hZ).obj (D.obj i)) :=
    ⟨Zi, IsHomLift.codomain_eq (cartesianProperFlatProjection B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).map (c.π.app i)) ε⟩
  obtain ⟨k, s, Xk, fk, hk, hpbk, hdimk⟩ :=
    h I D c hc i (ProperFlatFibre.space xi) (ProperFlatFibre.space xT)
      (ProperFlatFibre.str xi) (ProperFlatFibre.str xT) (ProperFlatFibre.map ε)
      (ProperFlatFibre.isAlgebraicSpace_space xi)
      (ProperFlatFibre.isQuasiCompactSpace_space B integerBase hZ _ xi
        (Space.isQuasiCompactSpace_yoneda_of_isAffine B integerBase hZ _ (D.obj i).property))
      (ProperFlatFibre.isPullback_map (x := xT) (y := xi) ε _)
      (ProperFlatFibre.isLocallyOfFiniteType_str B integerBase hZ _ xi)
      (ProperFlatFibre.hasRelativeDimensionLE_str B integerBase hZ _ xT 1 hdim)
  obtain ⟨Zk, δ, hδ⟩ :=
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ).exists_lift
      ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)) Zi xi.property
  have := hδ
  let xk : (cartesianProperFlatProjection B integerBase hZ).Fiber
      ((BigAffineFppf.inclusion B integerBase hZ).obj (D.obj k)) :=
    ⟨Zk, IsHomLift.domain_eq (cartesianProperFlatProjection B integerBase hZ)
      ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)) δ⟩
  have hsqk : IsPullback (ProperFlatFibre.str xk) (ProperFlatFibre.map δ)
      (yoneda.map ((BigAffineFppf.inclusion B integerBase hZ).map (D.map s)))
      (ProperFlatFibre.str xi) :=
    ProperFlatFibre.isPullback_map (x := xk) (y := xi) δ _
  refine ⟨k, s, Zk, δ, hδ,
    ProperFlatFibre.hasRelativeDimensionLE_of_str B integerBase hZ _ xk 1 ?_⟩
  exact Space.hasRelativeDimensionLE_of_iso B integerBase hZ (hpbk.isoIsPullback _ _ hsqk)
    (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id, hpbk.isoIsPullback_hom_fst])
    (ProperFlatFibre.isAlgebraicSpace_space xk)
    (isAlgebraicSpace_yoneda B integerBase hZ
      ((BigAffineFppf.inclusion B integerBase hZ).obj (D.obj k)))
    (isAlgebraicSpace_yoneda B integerBase hZ
      ((BigAffineFppf.inclusion B integerBase hZ).obj (D.obj k)))
    (ProperFlatFibre.isLocallyOfFiniteType_str B integerBase hZ _ xk) hdimk

/-- **The affine-base, size-free form of Stacks 0D4K, at index universes equal to the universe
of the schemes.** This is
`AlgebraicGeometry.Space.exists_hasRelativeDimensionLE_isPullback_of_limit` read as the
predicate the reduction of Stacks 0D55 consumes. -/
theorem descendsRelativeDimensionAlongAffineLimit_one :
    DescendsRelativeDimensionAlongAffineLimit.{u, u, u} B integerBase hZ 1 := by
  intro I _ _ D c hc i Xi XT fi fT g hXi hqc hpb hft hdimT
  exact Space.exists_hasRelativeDimensionLE_isPullback_of_limit B integerBase hZ D hc i 1 fi
    hXi hqc hft fT g hpb hdimT

/-- **Stacks 0D4K in the fibred category of finitely presented flat proper families.** Along an
affine cofiltered inverse limit in the big fppf site of `Spec(ℤ)`, a finitely presented flat
proper family over a stage whose base change to the vertex has relative dimension at most one
has base change to some later stage of relative dimension at most one.

This is the hypothesis `hdesc` of
`AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory`, discharged. -/
theorem descendsRelativeDimensionLEOne :
    DescendsRelativeDimensionLEOne.{u, u, u} B hZ :=
  descendsRelativeDimensionLEOne_of_descendsAlongAffineLimit B hZ
    (descendsRelativeDimensionAlongAffineLimit_one B hZ)

/-- **Stacks 0D55 reduced to Stacks 0D1I alone.** The stack of families of curves over the big
fppf site of `Spec(ℤ)` is limit preserving in the sense of Stacks 07XL as soon as the category
of finitely presented, flat and proper families of algebraic spaces is.

This is `AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory` with its second hypothesis,
the descent of the relative-dimension bound, discharged by
`AlgebraicGeometry.descendsRelativeDimensionLEOne`. -/
theorem isLimitPreserving_curvesFiberedCategory_of_properFlat
    (h0D1I : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (cartesianProperFlatFiberedCategory B integerBase hZ)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ) :=
  isLimitPreserving_curvesFiberedCategory B hZ (descendsRelativeDimensionLEOne B hZ) h0D1I

end Descent

end AlgebraicGeometry

end
