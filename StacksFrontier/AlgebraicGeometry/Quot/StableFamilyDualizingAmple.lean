module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.StableFibreDualizingAmple
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# Stability of a prestable family near a point and ampleness of `ω_{X/S}` (towards Stacks 0E74)

Let `f : X → S` be a prestable family of curves of genus `g ≥ 2` and let `s ∈ S`. Stacks 0E74
says that the fibre `X_s` has no rational tail and no rational bridge if and only if the relative
dualizing sheaf `ω_{X/S}` is ample on `f⁻¹(U)` for some open `U ∋ s`. The equivalence is proved
here from the results it cites:

* if `ω_{X/S}` is ample on `f⁻¹(U)`, its pullback `ω_{X_s}` to the fibre is ample, and an ample
  dualizing sheaf excludes rational tails and bridges (Stacks 0E63, 0E64 and 0B5Y);
* conversely if `X_s` has neither, `ω_{X_s}` is ample (Stacks 0E3P), and ampleness on the fibre
  spreads to a neighbourhood (Stacks 0D3D).

## Main definitions

* `AlgebraicGeometry.CurveFamily.residuePoint`, `AlgebraicGeometry.CurveFamily.residuePointMap`:
  the point `Spec κ(s) ⟶ S` of the base, as a morphism of the site.
* `AlgebraicGeometry.CurveFamily.IsFibrePresentation`: a cartesian square exhibiting a scheme
  `V` of the site as the fibre `X_s`.
* `AlgebraicGeometry.CurveFamily.fibreMap`: the structure morphism `V ⟶ Spec κ(s)` of such a
  presentation.
* `AlgebraicGeometry.HasNoRationalTailNoRationalBridge`: a scheme over a field has no rational
  tail and, once proper, no rational bridge (condition (1) of Stacks 0E74).
* `AlgebraicGeometry.CurveFamily.HasFibreGenus`,
  `AlgebraicGeometry.CurveFamily.IsDualizingOnFibres`: every fibre has genus `g`; a module
  restricts on every fibre to its dualizing sheaf.
* `AlgebraicGeometry.PrestableFibreReading`, `AlgebraicGeometry.OpenAmpleLocus`: the shapes of
  the two inputs on the family side (see the implementation notes).

## Main results

* `AlgebraicGeometry.CurveFamily.isRelativelyAmple_fibre_iff`: on a presentation of a fibre, the
  pullback of a module which restricts to the dualizing sheaf is ample over `Spec κ(s)` exactly
  when the dualizing sheaf of the fibre is invertible and ample.
* the argument of Stacks 0E74, both directions, from its inputs:
  `AlgebraicGeometry.CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of`

## Implementation notes

Every result Stacks 0E74 cites is taken here as an explicit input of the shape stated there:

* `h0E3P`, `h0E63`, `h0E64`: Stacks 0E3P, 0E63, 0E64, in the shapes
  `AlgebraicGeometry.DualizingAmpleOfNoRationalTailsBridges`,
  `AlgebraicGeometry.DegreeNegativeOnRationalTails` and
  `AlgebraicGeometry.DegreeZeroOnRationalBridges`;
* `h0D3D`: Stacks 0D3D, `AlgebraicGeometry.OpenAmpleLocus`, the conclusion of
  `AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`
  at the base `Spec ℤ`;
* `hpre`: the fibre reading of prestability, `AlgebraicGeometry.PrestableFibreReading` — a
  fibre of a prestable family over a field has at-worst-nodal singularities, dimension one and
  `H⁰ = κ(s)`; this is the base change of prestability (Stacks 0E6T) followed by part (2) of
  Stacks 0E6U;
* the relative dualizing sheaf: `ω` is any invertible module on `X` which restricts on every
  fibre `X_s` to the dualizing sheaf of Stacks 0BS2. That is what the relative dualizing sheaf
  of Stacks 0E6Q is, by Stacks 0E6R and the identification over a field in Section 0E6N; the
  definition of `ω_{X/S}` sits on Stacks 0E5X and 0E61.

The genus condition is used only at the point `s`; it is stated on every fibre, which is the
reading of "prestable of genus `g`" on points given by part (2) of Stacks 0E6V.

The fibre `X_s` is a priori an algebraic space; it is presented by a scheme `V` of the site with
a cartesian square over `Spec κ(s) ⟶ S`, as in `AlgebraicGeometry.IsStableCurveFamily` of
Stacks 0E75. Condition (1) asks for such a presentation without rational tails and bridges. In
the direction (2) ⟹ (1) the presentation is produced: ampleness over a neighbourhood makes the
fibre representable.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme over a field has no rational tail and, once it is proper over the field, no
rational bridge: condition (1) of Stacks 0E74. -/
abbrev HasNoRationalTailNoRationalBridge (k : Type u) [Field k] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of k)) : Prop :=
  letI : V.Over (Spec (.of k)) := ⟨f⟩
  (∀ C : V.IdealSheafData, ¬ IsRationalTail k V C) ∧
    ∀ hproper : IsProper (V ↘ Spec (.of k)),
      letI : IsProper (V ↘ Spec (.of k)) := hproper
      ∀ C : V.IdealSheafData, ¬ IsRationalBridge k V C

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

/-- The point `Spec κ(s)` of the base of a family of curves at a point `s`, as an object of the
site. -/
abbrev residuePoint (X : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : BigFppfOver B integerBase hZ :=
  Space.residueFieldObject B integerBase hZ X.base s
    (B.residueField_spec_contains X.base.left.property s)

/-- The morphism `Spec κ(s) ⟶ S` of the site. -/
abbrev residuePointMap (X : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : residuePoint B hZ X s ⟶ X.base :=
  Space.residueFieldMap B integerBase hZ X.base s
    (B.residueField_spec_contains X.base.left.property s)

/-- A *presentation of the fibre* `X_s` by a scheme `V` of the site: a cartesian square whose
right column is the family and whose bottom row is `Spec κ(s) ⟶ S`. -/
abbrev IsFibrePresentation (X : CurveFamily B hZ)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) {V : BigFppfOver B integerBase hZ}
    (v : V ⟶ residuePoint B hZ X s) (q : yoneda.obj V ⟶ X.total.obj) : Prop :=
  IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map (residuePointMap B hZ X s))

/-- The structure morphism `V ⟶ Spec κ(s)` of a presentation of a fibre. -/
abbrev fibreMap (X : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ residuePoint B hZ X s) :
    (BigFppfOver.toScheme B integerBase hZ).obj V ⟶
      Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)) :=
  (BigFppfOver.toScheme B integerBase hZ).map v

variable {B hZ}

/-- A presentation of a fibre of a family of curves is proper over the residue field: it is a
base change of the proper structure morphism. -/
theorem IsFibrePresentation.isProper {X : CurveFamily B hZ}
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (h : IsFibrePresentation B hZ X s v q) : IsProper (fibreMap B hZ X s v) :=
  Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ v
    (Space.isProper_of_isPullback B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ V)
      X.total.property (isAlgebraicSpace_yoneda B integerBase hZ _) (schemeSpace X.base).property
      h X.proper)

variable (B hZ)

/-- Every fibre of the family has genus `g`. -/
def HasFibreGenus (X : CurveFamily B hZ) (g : ℕ) : Prop :=
  ∀ (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (V : BigFppfOver B integerBase hZ)
    (v : V ⟶ residuePoint B hZ X s) (q : yoneda.obj V ⟶ X.total.obj),
    IsFibrePresentation B hZ X s v q → genus (fibreMap B hZ X s v) = g

/-- A module `ω` on the total space restricts on every fibre `X_s` to the dualizing sheaf of
Stacks 0BS2 of the fibre over `κ(s)`. -/
def IsDualizingOnFibres (X : CurveFamily B hZ)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.obj X.total.property) : Prop :=
  ∀ (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (V : BigFppfOver B integerBase hZ)
    (v : V ⟶ residuePoint B hZ X s) (q : yoneda.obj V ⟶ X.total.obj)
    (h : IsFibrePresentation B hZ X s v q),
    haveI := h.isProper
    Nonempty (Space.baseChangeModule B integerBase hZ ω V q ≅
      Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v))

end CurveFamily

/-- **The fibre reading of prestability** (input shape): a fibre of a prestable family over the
residue field of a point has at-worst-nodal singularities, dimension one and `H⁰ = κ(s)`. This
is the base change of prestability (Stacks 0E6T) followed by part (2) of Stacks 0E6U. -/
def PrestableFibreReading : Prop :=
  ∀ (X : CurveFamily B hZ), IsPrestableCurveFamily B hZ X →
    ∀ (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (V : BigFppfOver B integerBase hZ)
      (v : V ⟶ CurveFamily.residuePoint B hZ X s) (q : yoneda.obj V ⟶ X.total.obj),
      CurveFamily.IsFibrePresentation B hZ X s v q →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over
          (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
        ⟨CurveFamily.fibreMap B hZ X s v⟩
      Stacks.Curves.HasAtWorstNodalSingularities
          (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
          ((BigFppfOver.toScheme B integerBase hZ).obj V) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) = 1 ∧
        Function.Bijective (CurveFamily.fibreMap B hZ X s v).appTop

/-- **The open locus of relative ampleness** (input shape, Stacks 0D3D): for a proper morphism
`f : X ⟶ Y` of algebraic spaces and an invertible `𝒪_X`-module `L` there is an open subspace
`W ⊆ Y` such that a morphism `Y' ⟶ Y` factors through `W` exactly when the pullback of `L` to
`X' = Y' ×_Y X` is ample on `X'/Y'`. -/
def OpenAmpleLocus : Prop :=
  ∀ ⦃X Y : AlgebraicSpaces B integerBase hZ⦄ {f : X ⟶ Y},
    Space.IsProper B integerBase hZ f.hom →
    ∀ {L : Space.Modules.{u, u} B integerBase hZ X.1 X.2},
      Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ X.1 X.2).O)).property L →
      ∃ W : Subfunctor Y.1, Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ ⦃X' Y' : AlgebraicSpaces B integerBase hZ⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
          IsPullback p f' f g →
            ((∃ l : Y'.1 ⟶ W.toFunctor, l ≫ W.ι = g.hom) ↔
              Space.IsRelativelyAmple B integerBase hZ f'
                ((Space.modulePullback B integerBase hZ p).obj L))

namespace CurveFamily

variable {B hZ}

/-- **Ampleness on a fibre.** Let `ω` be an invertible module on the total space of a family of
curves which restricts on every fibre to the dualizing sheaf. On a presentation `V` of the fibre
`X_s`, the pullback of `ω` is ample over `Spec κ(s)` in the sense of algebraic spaces exactly when
the dualizing sheaf `ω_V` is invertible and ample. -/
theorem isRelativelyAmple_fibre_iff {X : CurveFamily B hZ}
    {ω : Space.Modules.{u, u} B integerBase hZ X.total.obj X.total.property}
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : IsDualizingOnFibres B hZ X ω)
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (h : IsFibrePresentation B hZ X s v q) :
    haveI := h.isProper
    Space.IsRelativelyAmple B integerBase hZ (schemeSpaceMap v)
        ((Space.modulePullback B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).obj ω) ↔
      ∃ _ : SheafOfModules.IsInvertible
          ((BigFppfOver.toScheme B integerBase hZ).obj V).toRingedSpace.presheaf
          (structureSheafRing
            ((BigFppfOver.toScheme B integerBase hZ).obj V).toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)),
        Scheme.Modules.IsAmple ((BigFppfOver.toScheme B integerBase hZ).obj V)
          (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) := by
  have := h.isProper
  obtain ⟨e⟩ := hω s V v q h
  let L' := (Space.modulePullback B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).obj ω
  let E : Space.baseChangeModule B integerBase hZ L' V (𝟙 _) ≅
      Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v) :=
    (Space.baseChangeModuleCompIso B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) ω V (𝟙 _)).symm ≪≫
      eqToIso (congrArg (Space.baseChangeModule B integerBase hZ ω V) (Category.id_comp q)) ≪≫ e
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (residuePoint B hZ X s)) :=
    inferInstanceAs (IsAffine (Spec _))
  constructor
  · intro hamp
    obtain ⟨hL, hrel⟩ := hamp.2 (residuePoint B hZ X s) V (𝟙 _) (𝟙 _) v
      (IsPullback.id_horiz (yoneda.map v))
    have : Stacks.Ample.IsInvertibleModule _
        (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E
    have hrel' := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mp hrel
    have hst := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      (fibreMap B hZ X s v) _).mp hrel'
    exact ⟨this, (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp hst⟩
  · rintro ⟨hinv, hamp⟩
    have hL'inv : Stacks.SheafOfModules.IsInvertible
        (Space.structurePresheaf B integerBase hZ (schemeSpace V).1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace V).1
            (schemeSpace V).2).O)).property L' :=
      Stacks.SheafOfModules.isInvertible_pullbackModules_obj
        (f := Space.smallEtaleRingedToposModulesHom B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)) (L := ω) (hL := hωinv)
    have : Stacks.Ample.IsInvertibleModule _
        (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) := hinv
    refine Space.isRelativelyAmple_of_exists_scheme _ L' hL'inv (residuePoint B hZ X s)
      (Iso.refl _) ⟨V, Iso.refl _, Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm,
        ?_⟩
    have h1 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      (fibreMap B hZ X s v) _).mpr ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hamp)
    have : Stacks.Ample.IsInvertibleModule _ (Space.baseChangeModule B integerBase hZ L' V (𝟙 _)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm
    have h2 := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mpr h1
    convert h2 using 2
    · rfl
    · refine (fun (m : V ⟶ residuePoint B hZ X s) (hm : m = v) =>
        (hm ▸ HEq.rfl : HEq ((BigFppfOver.toScheme B integerBase hZ).map m)
          (fibreMap B hZ X s v))) _ ?_
      apply yoneda.map_injective
      simp only [Functor.map_preimage, Iso.refl_hom, schemeSpaceMap_hom]
      exact (Category.id_comp _).trans (Category.comp_id _)
    · rfl

/-- **The argument of Stacks 0E74, from its inputs.** Let `f : X → S` be a prestable family of
curves whose fibres have genus `g ≥ 2`, let `ω` be an invertible module on `X` restricting on
every fibre to its dualizing sheaf (the relative dualizing sheaf `ω_{X/S}`), and let `s ∈ S`.
The following are equivalent:

1. the fibre `X_s` (presented by a scheme of the site) has no rational tail and no rational
   bridge;
2. there is an open `U ∋ s` of `S` such that `ω` is ample on `f⁻¹(U)` relative to `U`: on every
   base change of `f` along `U ⊆ S` the pullback of `ω` is relatively ample.

The inputs `h0E3P`, `h0E63`, `h0E64`, `h0D3D` and `hpre` are described in the module
docstring. -/
theorem hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of
    (h0E3P : DualizingAmpleOfNoRationalTailsBridges.{u})
    (h0E63 : DegreeNegativeOnRationalTails.{u}) (h0E64 : DegreeZeroOnRationalBridges.{u})
    (h0D3D : OpenAmpleLocus B hZ) (hpre : PrestableFibreReading B hZ)
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ)
    (hgen : X.HasFibreGenus B hZ g) (hg : 2 ≤ g)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.obj X.total.property)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : X.IsDualizingOnFibres B hZ ω)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ X.residuePoint B hZ s)
        (q : yoneda.obj V ⟶ X.total.obj),
        X.IsFibrePresentation B hZ s v q ∧
          HasNoRationalTailNoRationalBridge
            (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
            (X.fibreMap B hZ s v)) ↔
      ∃ U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens, s ∈ U ∧
        ∀ ⦃X₁ : AlgebraicSpaces B integerBase hZ⦄ (p₁ : X₁ ⟶ X.total)
          (f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)),
          IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)) →
            Space.IsRelativelyAmple B integerBase hZ f₁
              ((Space.modulePullback B integerBase hZ p₁).obj ω) := by
  obtain ⟨W, hW, hiff⟩ := h0D3D X.proper hωinv
  let K := X.residuePoint B hZ s
  let r := X.residuePointMap B hZ s
  have hfib : ∀ {V : BigFppfOver B integerBase hZ} (v : V ⟶ K) (q : yoneda.obj V ⟶ X.total.obj),
      X.IsFibrePresentation B hZ s v q →
      (HasNoRationalTailNoRationalBridge
          (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
          (X.fibreMap B hZ s v) ↔
        ∃ l : (schemeSpace K).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap r).hom) := by
    intro V v q h
    have := h.isProper
    let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over
        (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
      ⟨X.fibreMap B hZ s v⟩
    have : IsProper (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
        Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
      h.isProper
    obtain ⟨hnod, hdim, hbij⟩ := hpre X hX s V v q h
    have : IsIso (X.fibreMap B hZ s v).appTop :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso ((Scheme.ΓSpecIso (.of (((BigFppfOver.toScheme B integerBase hZ).obj
        X.base).residueField s))).inv ≫ (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
          Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField
            s))).appTop) :=
      inferInstanceAs (IsIso ((Scheme.ΓSpecIso _).inv ≫ (X.fibreMap B hZ s v).appTop))
    have hgV : 2 ≤ genus (X.fibreMap B hZ s v) := hgen s V v q h ▸ hg
    have hsq : IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v)
        X.toBase (schemeSpaceMap r) :=
      Space.isPullback_homMk B integerBase hZ X.total.property
        (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
        (isAlgebraicSpace_yoneda B integerBase hZ _) h
    refine Iff.trans ?_ (hiff (schemeSpaceMap r) _ _ hsq).symm
    refine Iff.trans ?_ (isRelativelyAmple_fibre_iff hωinv hω h).symm
    refine Iff.trans ?_
      (isAmple_dualizingSheafOverField_iff_noRationalTail_noRationalBridge_of h0E3P h0E63 h0E64
        hdim hnod hgV)
    exact and_congr_right fun _ => ⟨fun hb => hb inferInstance, fun hb _ => hb⟩
  have hmem : ∀ {T : BigFppfOver B integerBase hZ} (x : T ⟶ X.base),
      (∃ l : (schemeSpace T).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap x).hom) ↔
        ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map x) y ∈
          Space.opensOfOpenSubspace B integerBase hZ X.base W hW := by
    intro T x
    refine (Space.FinitePartUniversalOpen.exists_lift_iff_mem (X := yoneda.obj X.base) W T
      (yoneda.map x)).trans ?_
    rw [yonedaEquiv_yoneda_map]
    exact Space.mem_iff_of_isOpenSubspace B integerBase hZ X.base W hW x
  have hr : ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map r) y = s := fun y =>
    Scheme.fromSpecResidueField_apply _ _
  have hι : ∀ (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens) y,
      ((BigFppfOver.toScheme B integerBase hZ).map (Space.openSubHom X.base U)) y ∈ U := by
    intro U y
    rw [Space.toScheme_map_openSubHom]
    have hy := Set.mem_range_self (f := U.ι) y
    rwa [Scheme.Opens.range_ι] at hy
  constructor
  · rintro ⟨V, v, q, h, hno⟩
    obtain ⟨y⟩ : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj K) :=
      inferInstanceAs (Nonempty (Spec _))
    have hs := (hmem r).1 ((hfib v q h).1 hno) y
    rw [hr] at hs
    refine ⟨Space.opensOfOpenSubspace B integerBase hZ X.base W hW, hs, ?_⟩
    intro X₁ p₁ f₁ hsq
    refine (hiff _ p₁ f₁ hsq).1 ((hmem (Space.openSubHom X.base _)).2 (hι _))
  · rintro ⟨U, hsU, hamp⟩
    have sq₁ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap (Space.openSubHom X.base U))
    have hUW := (hmem (Space.openSubHom X.base U)).1 ((hiff _ _ _ sq₁).2 (hamp _ _ sq₁))
    have hsW : s ∈ Space.opensOfOpenSubspace B integerBase hZ X.base W hW := by
      have := hUW ⟨s, hsU⟩
      rwa [Space.toScheme_map_openSubHom] at this
    have hrW : ∃ l : (schemeSpace K).1 ⟶ W.toFunctor, l ≫ W.ι = (schemeSpaceMap r).hom :=
      (hmem r).2 fun y => (hr y).symm ▸ hsW
    have sq₀ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap r)
    have hamp₀ := (hiff _ _ _ sq₀).1 hrW
    obtain ⟨V, v, q', hsq'⟩ := hamp₀.1 (𝟙 (yoneda.obj K))
    have h : X.IsFibrePresentation B hZ s v (q' ≫ pullback.fst X.toBase.hom (yoneda.map r)) := by
      have := hsq'.paste_horiz (AlgebraicSpaces.isPullback_hom B integerBase hZ sq₀)
      have e : 𝟙 (yoneda.obj K) ≫ (schemeSpaceMap r).hom = yoneda.map r :=
        Category.id_comp (yoneda.map r)
      exact cast (congrArg (fun t : yoneda.obj K ⟶ yoneda.obj X.base =>
        IsPullback (q' ≫ pullback.fst X.toBase.hom (yoneda.map r)) (yoneda.map v) X.toBase.hom t)
          e) this
    exact ⟨V, v, _, h, (hfib v _ h).2 hrW⟩

end CurveFamily

end AlgebraicGeometry

end
