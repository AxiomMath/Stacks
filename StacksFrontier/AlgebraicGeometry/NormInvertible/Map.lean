module

public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Coefficient
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Vanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# The norm of a map of invertible modules

Let `f : X ⟶ Y` be a finite morphism of schemes with a norm `N` on functions and
let `φ : L ⟶ L'` be a map of invertible `𝒪_X`-modules. On a target open `V` over which both `L`
and `L'` are trivialized upstairs, choose generators `s`, `t` and write `φ(s) = a t`; then
`Norm(φ)` is multiplication by `N(a)` in the frames `Norm(s)`, `Norm(t)` of `Norm(L)`,
`Norm(L')`. This file shows those local maps agree on overlaps, glues them, and identifies the
vanishing locus of the result: `Norm(φ)` vanishes at `y` exactly when `φ` vanishes somewhere in
the fibre over `y`.

This is [Stacks, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ).

## The construction and its hypothesis-free form

The gluing is carried out from an explicit trivializing cover of the target for each of `L` and
`L'` — the hypothesis `Stacks.Divisors.HasTrivializingTargetCover`, which is verbatim the
conclusion of [Stacks, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT). Nothing else is
assumed there: no invertibility instance, no Picard group, no cohomology. Those are the
`normMapOfCover` declarations.

For an invertible `L` and `L'` the two covers are *theorems*, by
`Stacks.Divisors.hasTrivializingTargetCover_of_isFinite`, so the hypotheses disappear and the
statements become Tag 0BCZ's own. Those are `normMap`, `normMap_generator` and
`normMap_zeroAt_iff`, and they carry the tag. Both forms are kept: a consumer holding a cover
but no invertibility instance can use the first, and the covers are propositions, so the two
agree on the nose when both apply.

## No degree is required

As in `Basic.lean`, the `normMapOfCover` layer takes a `Stacks.Norm.MorphismNormMap`: only
multiplicativity, naturality and the vanishing axiom are used. The tagged declarations
`normMap`, `normMap_generator` and `normMap_zeroAt_iff` keep Tag 0BCZ's own hypothesis, a
`Stacks.Norm.MorphismNorm` of degree `d`, and pass its underlying norm map down.

## Main definitions

* `Stacks.SheafOfModules.localGeneratorMap`: on a trivializing open, the map of modules
  carrying one chosen generator to a coefficient times another.
* `Stacks.Divisors.NormMapChart`: a target open with a pair of frames above it.
* `Stacks.Divisors.normMapOfCover` and `Stacks.Divisors.normMap`: the norm of `φ`, from
  explicit trivializing covers and from invertibility.

## Main results

* `Stacks.Divisors.hasTrivializingTargetCover_of_isInvertible`: Tag 0BUT, for invertibility in
  the `AlgebraicGeometry.SheafOfModules.IsInvertible` spelling of Tag 01CS.
* `Stacks.Divisors.normMap_generator`: in local frames the norm map is multiplication by the
  norm of the coefficient. This pins the map down rather than merely asserting its existence.
* `Stacks.Divisors.normMap_zeroAt_iff`: the vanishing locus of the norm map is the image of the
  vanishing locus of `φ`.

## Implementation notes

The local maps are assembled by the sheaf condition for `Norm(L')` rather than by a cocycle: for
each open `U` the section over `U` is the unique one restricting, on every chart inside `U`, to
the image of the restricted section under that chart's local map (`existsUnique_normSection`).
Compatibility of the local maps on overlaps is `normChartMap_restrict`, and it rests on two
facts — the coefficient commutes with restriction, so its norm does by naturality of `N`; and
the local map does not depend on the chosen frames, which is
`normLocalGeneratorMap_frameInvariant`, the statement that a change of frames multiplies the
coefficient downstairs by the *norms* of the two upstairs ratios.

The vanishing locus is then immediate from two inputs that are proved elsewhere and are both
independent of this gluing: that vanishing at a point can be read in any frame around it
(`Stacks.SheafOfModules.zeroAt_iff_evaluation_eq_zero`), and that the norm of a function
vanishes at `y` exactly when the function vanishes in the fibre
(`Stacks.Divisors.evaluation_norm_eq_zero_iff_exists_zero_in_fibre`).

The repository carries two Tag 01CS invertibility classes with identical definitions, and
`hasTrivializingTargetCover_of_isFinite` consumes the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean` while Tag 0BCZ is stated
with the one of `StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`. Neither discharges the
other by instance search, so `hasTrivializingTargetCover_of_isInvertible` crosses once, through
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`; nothing below restates anything on
either side of that bridge.

## References

* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BUT](https://stacks.math.columbia.edu/tag/0BUT)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

section LocalMap

variable {X : RingedSpace.{u, u}}

/-- Restriction of a section of a sheaf of modules is transitive. -/
theorem module_restrict_comp (M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    {U V W : Opens X.carrier} (h : V ≤ U) (k : W ≤ V) (m : M.val.obj (op U)) :
    M.val.map (homOfLE k).op (M.val.map (homOfLE h).op m) =
      M.val.map (homOfLE (k.trans h)).op m := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Restricting a section along the identity inclusion does nothing. -/
theorem module_restrict_self (M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (U : Opens X.carrier) (m : M.val.obj (op U)) :
    M.val.map (homOfLE (le_rfl : U ≤ U)).op m = m := by
  rw [show (homOfLE (le_rfl : U ≤ U)).op = 𝟙 (op U) from Subsingleton.elim _ _,
    M.val.map_id]
  rfl

variable (L L' : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-- A chosen generator identifies the sections of a module on every smaller open with the
sections of the structure sheaf there. -/
noncomputable def generatorLinearEquiv {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) :
    (structureSheaf X.sheaf).obj.obj (op V) ≃ₗ[(structureSheaf X.sheaf).obj.obj (op V)]
      L.val.obj (op V) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ (L.val.restrictₛₗ (homOfLE h).op s.val))
    (s.property V h)

/-- On a trivializing open, multiplication by a coefficient is the unique map of modules
carrying one chosen generator to that coefficient times another. -/
noncomputable def localGeneratorMap {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U)
    (b : (structureSheaf X.sheaf).obj.obj (op V)) :
    L.val.obj (op V) →ₗ[(structureSheaf X.sheaf).obj.obj (op V)] L'.val.obj (op V) :=
  (generatorLinearEquiv L' h t).toLinearMap.comp
    ((LinearMap.mulRight ((structureSheaf X.sheaf).obj.obj (op V)) b).comp
      (generatorLinearEquiv L h s).symm.toLinearMap)

/-- On a trivializing open, the local map carries the restricted generator of `L` to the
coefficient times the restricted generator of `L'`. -/
theorem localGeneratorMap_generator {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U)
    (b : (structureSheaf X.sheaf).obj.obj (op V)) :
    localGeneratorMap L L' h s t b (L.val.restrictₛₗ (homOfLE h).op s.val) =
      b • L'.val.restrictₛₗ (homOfLE h).op t.val := by
  have hS : generatorLinearEquiv L h s 1 = L.val.restrictₛₗ (homOfLE h).op s.val := by
    change (1 : (structureSheaf X.sheaf).obj.obj (op V)) •
      L.val.restrictₛₗ (homOfLE h).op s.val = _
    rw [one_smul]
  change (generatorLinearEquiv L' h t)
      ((LinearMap.mulRight ((structureSheaf X.sheaf).obj.obj (op V)) b)
        ((generatorLinearEquiv L h s).symm (L.val.restrictₛₗ (homOfLE h).op s.val))) =
    b • L'.val.restrictₛₗ (homOfLE h).op t.val
  rw [← hS, (generatorLinearEquiv L h s).symm_apply_apply]
  simp only [LinearMap.mulRight_apply, one_mul]
  rfl

/-- On the same open, the local map carries the generator of `L` to the coefficient times the
generator of `L'`. -/
private theorem localGeneratorMap_self_generator {U : Opens X.carrier}
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U)
    (b : (structureSheaf X.sheaf).obj.obj (op U)) :
    localGeneratorMap L L' (le_rfl : U ≤ U) s t b s.val = b • t.val := by
  simpa only [generator_restrict_self] using localGeneratorMap_generator L L' le_rfl s t b

/-- The local maps are independent of the chosen frames when the coefficients transform by the
two generator ratios. -/
theorem localGeneratorMap_eq_of_change {U V : Opens X.carrier} (h : V ≤ U)
    (s s' : GeneratorSections X L U) (t t' : GeneratorSections X L' U)
    (c d a a' : (structureSheaf X.sheaf).obj.obj (op V))
    (hs : L.val.restrictₛₗ (homOfLE h).op s'.val =
      c • L.val.restrictₛₗ (homOfLE h).op s.val)
    (ht : L'.val.restrictₛₗ (homOfLE h).op t'.val =
      d • L'.val.restrictₛₗ (homOfLE h).op t.val)
    (ha : a' * d = c * a) :
    localGeneratorMap L L' h s t a = localGeneratorMap L L' h s' t' a' := by
  have hgen : localGeneratorMap L L' h s t a (L.val.restrictₛₗ (homOfLE h).op s'.val) =
      localGeneratorMap L L' h s' t' a' (L.val.restrictₛₗ (homOfLE h).op s'.val) := by
    rw [localGeneratorMap_generator L L' h s' t' a', hs,
      (localGeneratorMap L L' h s t a).map_smul, localGeneratorMap_generator, smul_smul, ht,
      smul_smul, ha]
  refine LinearMap.ext fun m => ?_
  obtain ⟨r, hr⟩ := (s'.property V h).surjective m
  rw [← hr, (localGeneratorMap L L' h s t a).map_smul,
    (localGeneratorMap L L' h s' t' a').map_smul, hgen]

/-- The local maps commute with restriction of both the coefficient and the section. -/
theorem localGeneratorMap_restrict_apply {U V : Opens X.carrier} (h : V ≤ U)
    (s : GeneratorSections X L U) (t : GeneratorSections X L' U)
    (b : (structureSheaf X.sheaf).obj.obj (op U)) (m : L.val.obj (op U)) :
    L'.val.restrictₛₗ (homOfLE h).op (localGeneratorMap L L' (le_rfl : U ≤ U) s t b m) =
      localGeneratorMap L L' (le_rfl : V ≤ V) (generatorRestrict L h s)
        (generatorRestrict L' h t) ((structureSheaf X.sheaf).obj.map (homOfLE h).op b)
        (L.val.restrictₛₗ (homOfLE h).op m) := by
  obtain ⟨r, hr⟩ := (s.property U le_rfl).surjective m
  have hm : m = r • s.val := by
    simpa only [generator_restrict_self] using hr.symm
  subst hm
  have e1 : localGeneratorMap L L' (le_rfl : U ≤ U) s t b (r • s.val) = r • (b • t.val) := by
    rw [(localGeneratorMap L L' (le_rfl : U ≤ U) s t b).map_smul,
      localGeneratorMap_self_generator]
  have e2 : L.val.map (homOfLE h).op (r • s.val) =
      ((structureSheaf X.sheaf).obj.map (homOfLE h).op r) • (generatorRestrict L h s).val :=
    L.val.map_smul _ _ _
  change L'.val.map (homOfLE h).op
      (localGeneratorMap L L' (le_rfl : U ≤ U) s t b (r • s.val)) =
    localGeneratorMap L L' (le_rfl : V ≤ V) (generatorRestrict L h s)
      (generatorRestrict L' h t) ((structureSheaf X.sheaf).obj.map (homOfLE h).op b)
      (L.val.map (homOfLE h).op (r • s.val))
  rw [e1, e2, (localGeneratorMap L L' (le_rfl : V ≤ V) (generatorRestrict L h s)
      (generatorRestrict L' h t)
      ((structureSheaf X.sheaf).obj.map (homOfLE h).op b)).map_smul,
      localGeneratorMap_self_generator,
    L'.val.map_smul, L'.val.map_smul]
  rfl

end LocalMap

end Stacks.SheafOfModules

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}}

/-- A trivializing target cover supplies a generator of `L` above a neighbourhood of every
point of the target. -/
theorem exists_generatorSections_near_point (f : X ⟶ Y) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧ Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)) := by
  obtain ⟨V, hyV, e⟩ := hL y
  exact ⟨V, hyV, ⟨normChartSourceGenerator f L ⟨V, e⟩⟩⟩

/-- A target open together with a frame for `L` and one for `L'` above it. -/
abbrev NormMapChart (f : X ⟶ Y) (L L' : X.Modules) :=
  Σ V : Y.Opens, GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V) ×
    GeneratorSections X.toRingedSpace L' (f ⁻¹ᵁ V)

/-- The charts contained in a given target open. -/
abbrev NormMapChartsIn (f : X ⟶ Y) (L L' : X.Modules) (U : Y.Opens) :=
  {c : NormMapChart f L L' // c.1 ≤ U}

/-- The charts inside any target open cover it. -/
theorem normMapCharts_cover (f : X ⟶ Y) (L L' : X.Modules)
    (hL : HasTrivializingTargetCover f L) (hL' : HasTrivializingTargetCover f L')
    (U : Y.Opens) : U ≤ iSup (fun c : NormMapChartsIn f L L' U => c.1.1) := by
  intro y hy
  obtain ⟨V₁, hy₁, ⟨s₁⟩⟩ := exists_generatorSections_near_point f L hL y
  obtain ⟨V₂, hy₂, ⟨t₂⟩⟩ := exists_generatorSections_near_point f L' hL' y
  have hV₁ : f ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ U) ≤ f ⁻¹ᵁ V₁ := fun x hx => hx.1.1
  have hV₂ : f ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ U) ≤ f ⁻¹ᵁ V₂ := fun x hx => hx.1.2
  exact Opens.mem_iSup.mpr
    ⟨⟨⟨V₁ ⊓ V₂ ⊓ U, generatorRestrict (X := X.toRingedSpace) L hV₁ s₁,
        generatorRestrict (X := X.toRingedSpace) L' hV₂ t₂⟩, inf_le_right⟩,
      ⟨⟨hy₁, hy₂⟩, hy⟩⟩

section Cover

variable (f : X ⟶ Y) (N : MorphismNormMap f) (L L' : X.Modules)
  (hL : HasTrivializingTargetCover f L) (hL' : HasTrivializingTargetCover f L')
  (φ : L ⟶ L')

/-- A frame change upstairs multiplies the restricted normed frame by the norm of the ratio. -/
private theorem normGenerator_restrict_smul (V : Y.Opens) (M : X.Modules)
    (hM : HasTrivializingTargetCover f M)
    (s s' : GeneratorSections X.toRingedSpace M (f ⁻¹ᵁ V)) (c : Γ(X, f ⁻¹ᵁ V))
    (hs : s'.val = @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ V)))
      (M.val.obj (op (f ⁻¹ᵁ V))) _ c s.val) :
    (normInvertible f N M).val.restrictₛₗ (homOfLE (le_rfl : V ≤ V)).op
      (normGenerator f N M hM V s').val =
      @SMul.smul ((structureSheaf Y.sheaf).obj.obj (op V))
        ((normInvertible f N M).val.obj (op V)) _ (N.app V c)
        ((normInvertible f N M).val.restrictₛₗ (homOfLE (le_rfl : V ≤ V)).op
          (normGenerator f N M hM V s).val) := by
  rw [generator_restrict_self (X := Y.toRingedSpace) _ V (normGenerator f N M hM V s'),
    generator_restrict_self (X := Y.toRingedSpace) _ V (normGenerator f N M hM V s)]
  exact normGenerator_smul f N M hM V s s' c hs

/-- Changing the upstairs frames does not change the local map on the norm modules: the
coefficient downstairs is multiplied by the norms of the two upstairs ratios. -/
theorem normLocalGeneratorMap_eq_of_change (V : Y.Opens)
    (s s' : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V))
    (t t' : GeneratorSections X.toRingedSpace L' (f ⁻¹ᵁ V))
    (c e a a' : Γ(X, f ⁻¹ᵁ V))
    (hs : s'.val = @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ V)))
      (L.val.obj (op (f ⁻¹ᵁ V))) _ c s.val)
    (ht : t'.val = @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ V)))
      (L'.val.obj (op (f ⁻¹ᵁ V))) _ e t.val)
    (ha : φ.val.app (op (f ⁻¹ᵁ V)) s.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ V)))
        (L'.val.obj (op (f ⁻¹ᵁ V))) _ a t.val)
    (ha' : φ.val.app (op (f ⁻¹ᵁ V)) s'.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ V)))
        (L'.val.obj (op (f ⁻¹ᵁ V))) _ a' t'.val) :
    localGeneratorMap (normInvertible f N L) (normInvertible f N L') (le_rfl : V ≤ V)
        (normGenerator f N L hL V s) (normGenerator f N L' hL' V t) (N.app V a) =
      localGeneratorMap (normInvertible f N L) (normInvertible f N L') (le_rfl : V ≤ V)
        (normGenerator f N L hL V s') (normGenerator f N L' hL' V t') (N.app V a') := by
  have hcoeff := generatorCoefficient_change (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V)
    s s' t t' c e a a' hs ht ha ha'
  have hgenS' := normGenerator_restrict_smul f N V L hL s s' c hs
  have hgenT' := normGenerator_restrict_smul f N V L' hL' t t' e ht
  have hcoeffN : N.app V a' * N.app V e = N.app V c * N.app V a :=
    calc N.app V a' * N.app V e = N.app V (a' * e) := ((N.app V).map_mul a' e).symm
      _ = N.app V (c * a) := congrArg (N.app V) hcoeff
      _ = N.app V c * N.app V a := (N.app V).map_mul c a
  exact localGeneratorMap_eq_of_change (normInvertible f N L) (normInvertible f N L') le_rfl
    (normGenerator f N L hL V s) (normGenerator f N L hL V s')
    (normGenerator f N L' hL' V t) (normGenerator f N L' hL' V t')
    (N.app V c) (N.app V e) (N.app V a) (N.app V a') hgenS' hgenT' hcoeffN

/-- The local map on the norm modules does not depend on the chosen upstairs frames. -/
theorem normLocalGeneratorMap_frameInvariant (V : Y.Opens)
    (s s' : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V))
    (t t' : GeneratorSections X.toRingedSpace L' (f ⁻¹ᵁ V)) :
    localGeneratorMap (normInvertible f N L) (normInvertible f N L') (le_rfl : V ≤ V)
        (normGenerator f N L hL V s) (normGenerator f N L' hL' V t)
        (N.app V (generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V) s t)) =
      localGeneratorMap (normInvertible f N L) (normInvertible f N L') (le_rfl : V ≤ V)
        (normGenerator f N L hL V s') (normGenerator f N L' hL' V t')
        (N.app V (generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V) s' t')) := by
  obtain ⟨c, hc, -⟩ := exists_isUnit_smul_generator (X := X.toRingedSpace) L (f ⁻¹ᵁ V) s s'
  obtain ⟨e, he, -⟩ := exists_isUnit_smul_generator (X := X.toRingedSpace) L' (f ⁻¹ᵁ V) t t'
  exact normLocalGeneratorMap_eq_of_change f N L L' hL hL' φ V s s' t t' c e _ _ hc he
    (generatorCoefficient_spec (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V) s t)
    (generatorCoefficient_spec (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V) s' t')

/-- The local norm map attached to a chart. -/
noncomputable abbrev normChartMap (c : NormMapChart f L L') :=
  localGeneratorMap (normInvertible f N L) (normInvertible f N L') le_rfl
    (normGenerator f N L hL c.1 c.2.1) (normGenerator f N L' hL' c.1 c.2.2)
    (N.app c.1 (generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ c.1) c.2.1 c.2.2))

/-- The local norm maps of two nested charts agree. -/
theorem normChartMap_restrict (c e : NormMapChart f L L') (h : e.1 ≤ c.1)
    (m : (normInvertible f N L).val.obj (op c.1)) :
    (normInvertible f N L').val.map (homOfLE h).op (normChartMap f N L L' hL hL' φ c m) =
      normChartMap f N L L' hL hL' φ e
        ((normInvertible f N L).val.map (homOfLE h).op m) := by
  have hX : f ⁻¹ᵁ e.1 ≤ f ⁻¹ᵁ c.1 := (Opens.map f.base).monotone h
  set s := generatorRestrict (X := X.toRingedSpace) L hX c.2.1 with hsdef
  set t := generatorRestrict (X := X.toRingedSpace) L' hX c.2.2 with htdef
  have hs : generatorRestrict (X := Y.toRingedSpace) (normInvertible f N L) h
      (normGenerator f N L hL c.1 c.2.1) = normGenerator f N L hL e.1 s :=
    Subtype.ext (normGenerator_restrict f N L hL h c.2.1).symm
  have ht : generatorRestrict (X := Y.toRingedSpace) (normInvertible f N L') h
      (normGenerator f N L' hL' c.1 c.2.2) = normGenerator f N L' hL' e.1 t :=
    Subtype.ext (normGenerator_restrict f N L' hL' h c.2.2).symm
  have ha : N.app e.1 (generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ e.1) s t) =
      (structureSheaf Y.sheaf).obj.map (homOfLE h).op
        (N.app c.1 (generatorCoefficient (X := X.toRingedSpace) L L' φ
          (f ⁻¹ᵁ c.1) c.2.1 c.2.2)) := by
    rw [hsdef, htdef, generatorCoefficient_restrict (X := X.toRingedSpace) L L' φ hX c.2.1 c.2.2]
    exact N.naturality (homOfLE h) _
  have hmap : localGeneratorMap (normInvertible f N L) (normInvertible f N L')
        (le_rfl : e.1 ≤ e.1)
        (generatorRestrict (X := Y.toRingedSpace) (normInvertible f N L) h
          (normGenerator f N L hL c.1 c.2.1))
        (generatorRestrict (X := Y.toRingedSpace) (normInvertible f N L') h
          (normGenerator f N L' hL' c.1 c.2.2))
        ((structureSheaf Y.sheaf).obj.map (homOfLE h).op
          (N.app c.1 (generatorCoefficient (X := X.toRingedSpace) L L' φ
            (f ⁻¹ᵁ c.1) c.2.1 c.2.2))) =
      localGeneratorMap (normInvertible f N L) (normInvertible f N L') (le_rfl : e.1 ≤ e.1)
        (normGenerator f N L hL e.1 e.2.1) (normGenerator f N L' hL' e.1 e.2.2)
        (N.app e.1 (generatorCoefficient (X := X.toRingedSpace) L L' φ
          (f ⁻¹ᵁ e.1) e.2.1 e.2.2)) := by
    rw [hs, ht, ← ha]
    exact normLocalGeneratorMap_frameInvariant f N L L' hL hL' φ e.1 s e.2.1 t e.2.2
  refine (localGeneratorMap_restrict_apply (X := Y.toRingedSpace) (normInvertible f N L)
    (normInvertible f N L') h (normGenerator f N L hL c.1 c.2.1)
    (normGenerator f N L' hL' c.1 c.2.2)
    (N.app c.1 (generatorCoefficient (X := X.toRingedSpace) L L' φ
      (f ⁻¹ᵁ c.1) c.2.1 c.2.2)) m).trans ?_
  exact LinearMap.congr_fun hmap _

include hL hL' in
/-- Two sections of the norm of `L'` agreeing on every chart are equal. -/
theorem normSections_ext (U : Y.Opens) (a b : (normInvertible f N L').val.obj (op U))
    (h : ∀ (c : NormMapChart f L L') (hc : c.1 ≤ U),
      (normInvertible f N L').val.map (homOfLE hc).op a =
        (normInvertible f N L').val.map (homOfLE hc).op b) : a = b := by
  let F : TopCat.Sheaf AddCommGrpCat Y :=
    ⟨(normInvertible f N L').val.presheaf, (normInvertible f N L').isSheaf⟩
  exact F.eq_of_locally_eq' (fun c : NormMapChartsIn f L L' U => c.1.1) U
    (fun c => homOfLE c.2) (normMapCharts_cover f L L' hL hL' U) a b fun c => h c.1 c.2

/-- The unique section of the norm of `L'` whose restriction to every chart is given by that
chart's local norm map. -/
theorem existsUnique_normSection (U : Y.Opens) (m : (normInvertible f N L).val.obj (op U)) :
    ∃! n : (normInvertible f N L').val.obj (op U),
      ∀ (c : NormMapChart f L L') (h : c.1 ≤ U),
        (normInvertible f N L').val.map (homOfLE h).op n =
          normChartMap f N L L' hL hL' φ c
            ((normInvertible f N L).val.map (homOfLE h).op m) := by
  let F : TopCat.Sheaf AddCommGrpCat Y :=
    ⟨(normInvertible f N L').val.presheaf, (normInvertible f N L').isSheaf⟩
  have hc : TopCat.Presheaf.IsCompatible F.obj
      (fun c : NormMapChartsIn f L L' U => c.1.1)
      (fun c => normChartMap f N L L' hL hL' φ c.1
        ((normInvertible f N L).val.map (homOfLE c.2).op m)) := by
    intro c e
    set q : NormMapChart f L L' := ⟨c.1.1 ⊓ e.1.1,
      generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).monotone inf_le_left) c.1.2.1,
      generatorRestrict (X := X.toRingedSpace) L' ((Opens.map f.base).monotone inf_le_left)
        c.1.2.2⟩ with hq
    have hmid : (normInvertible f N L).val.map
          (homOfLE (show q.1 ≤ c.1.1 from inf_le_left)).op
          ((normInvertible f N L).val.map (homOfLE c.2).op m) =
        (normInvertible f N L).val.map
          (homOfLE (show q.1 ≤ e.1.1 from inf_le_right)).op
          ((normInvertible f N L).val.map (homOfLE e.2).op m) :=
      (module_restrict_comp (normInvertible f N L) c.2
          (show q.1 ≤ c.1.1 from inf_le_left) m).trans
        (module_restrict_comp (normInvertible f N L) e.2
          (show q.1 ≤ e.1.1 from inf_le_right) m).symm
    exact (normChartMap_restrict f N L L' hL hL' φ c.1 q inf_le_left _).trans
      ((congrArg (fun z => normChartMap f N L L' hL hL' φ q z) hmid).trans
        (normChartMap_restrict f N L L' hL hL' φ e.1 q inf_le_right _).symm)
  obtain ⟨n, hn, hu⟩ := F.existsUnique_gluing'
    (fun c : NormMapChartsIn f L L' U => c.1.1) U (fun c => homOfLE c.2)
    (normMapCharts_cover f L L' hL hL' U) _ hc
  exact ⟨n, fun c h => hn ⟨c, h⟩, fun n' hn' => hu n' fun c => hn' c.1 c.2⟩

/-- The value of the norm map on a section. -/
noncomputable def normSection (U : Y.Opens) (m : (normInvertible f N L).val.obj (op U)) :
    (normInvertible f N L').val.obj (op U) :=
  (existsUnique_normSection f N L L' hL hL' φ U m).choose

/-- On every chart inside the open, the value of the norm map restricts to the chart's local norm
map applied to the restricted section. -/
theorem normSection_spec (U : Y.Opens) (m : (normInvertible f N L).val.obj (op U))
    (c : NormMapChart f L L') (h : c.1 ≤ U) :
    (normInvertible f N L').val.map (homOfLE h).op (normSection f N L L' hL hL' φ U m) =
      normChartMap f N L L' hL hL' φ c ((normInvertible f N L).val.map (homOfLE h).op m) :=
  (existsUnique_normSection f N L L' hL hL' φ U m).choose_spec.1 c h

/-- The value of the norm map commutes with restriction to a smaller open. -/
theorem normSection_restrict {U V : Y.Opens} (h : V ≤ U)
    (m : (normInvertible f N L).val.obj (op U)) :
    (normInvertible f N L').val.map (homOfLE h).op (normSection f N L L' hL hL' φ U m) =
      normSection f N L L' hL hL' φ V ((normInvertible f N L).val.map (homOfLE h).op m) := by
  refine normSections_ext f N L L' hL hL' V _ _ fun c hc => ?_
  rw [module_restrict_comp (normInvertible f N L') h hc
      (normSection f N L L' hL hL' φ U m),
    normSection_spec f N L L' hL hL' φ U m c (hc.trans h),
    normSection_spec f N L L' hL hL' φ V
      ((normInvertible f N L).val.map (homOfLE h).op m) c hc,
    module_restrict_comp (normInvertible f N L) h hc m]

/-- The norm map on the sections over a target open, as a linear map. -/
noncomputable def normSectionLinearMap (U : Y.Opens) :
    (normInvertible f N L).val.obj (op U) →ₗ[(structureSheaf Y.sheaf).obj.obj (op U)]
      (normInvertible f N L').val.obj (op U) where
  toFun := normSection f N L L' hL hL' φ U
  map_add' m n := by
    refine normSections_ext f N L L' hL hL' U _ _ fun c hc => ?_
    simp only [map_add, normSection_spec]
    exact (normChartMap f N L L' hL hL' φ c).map_add _ _
  map_smul' r m := by
    refine normSections_ext f N L L' hL hL' U _ _ fun c hc => ?_
    change (normInvertible f N L').val.map (homOfLE hc).op
        (normSection f N L L' hL hL' φ U (r • m)) =
      (normInvertible f N L').val.map (homOfLE hc).op
        (r • normSection f N L L' hL hL' φ U m)
    rw [normSection_spec, PresheafOfModules.map_smul, PresheafOfModules.map_smul,
      normSection_spec]
    exact (normChartMap f N L L' hL hL' φ c).map_smul _ _

/-- **The norm of a map of invertible modules**, the first assertion of Tag 0BCZ, from an
explicit trivializing target cover for each of `L` and `L'`. For an invertible `L` and `L'` the
covers are supplied by Tag 0BUT and the hypotheses disappear; that is `normMap`, which carries
the tag. -/
noncomputable def normMapOfCover : normInvertible f N L ⟶ normInvertible f N L' := by
  refine ⟨{ app := fun U => ModuleCat.ofHom (normSectionLinearMap f N L L' hL hL' φ U.unop)
            naturality := ?_ }⟩
  intro U V i
  ext m
  exact (normSection_restrict f N L L' hL hL' φ i.unop.le m).symm

/-- **In local frames the norm map is multiplication by the norm of the coefficient**, the
local-generator formula of Tag 0BCZ, from explicit trivializing target covers. -/
theorem normMapOfCover_generator (U : Y.Opens)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U))
    (t : GeneratorSections X.toRingedSpace L' (f ⁻¹ᵁ U)) (a : Γ(X, f ⁻¹ᵁ U))
    (ha : φ.val.app (op (f ⁻¹ᵁ U)) s.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ U)))
        (L'.val.obj (op (f ⁻¹ᵁ U))) _ a t.val) :
    (normMapOfCover f N L L' hL hL' φ).val.app (op U) (normGenerator f N L hL U s).val =
      @SMul.smul ((structureSheaf Y.sheaf).obj.obj (op U))
        ((normInvertible f N L').val.obj (op U)) _ (N.app U a)
        (normGenerator f N L' hL' U t).val := by
  have hc : generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ U) s t = a :=
    generatorCoefficient_unique (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ U) s t a ha
  have h := normSection_spec f N L L' hL hL' φ U (normGenerator f N L hL U s).val ⟨U, s, t⟩ le_rfl
  rw [module_restrict_self (normInvertible f N L') U
      (normSection f N L L' hL hL' φ U (normGenerator f N L hL U s).val),
    module_restrict_self (normInvertible f N L) U (normGenerator f N L hL U s).val] at h
  have hg := localGeneratorMap_self_generator (normInvertible f N L) (normInvertible f N L')
    (normGenerator f N L hL U s) (normGenerator f N L' hL' U t) (N.app U a)
  have hmap : normChartMap f N L L' hL hL' φ ⟨U, s, t⟩ =
      localGeneratorMap (normInvertible f N L) (normInvertible f N L') (le_rfl : U ≤ U)
        (normGenerator f N L hL U s) (normGenerator f N L' hL' U t) (N.app U a) := by
    dsimp only [normChartMap]
    rw [hc]
  change normSection f N L L' hL hL' φ U (normGenerator f N L hL U s).val = _
  rw [h, hmap]
  exact hg

/-- **The norm map vanishes at `y` exactly when the original map vanishes at some point of the
fibre over `y`**, the vanishing-locus clause of Tag 0BCZ, from explicit trivializing target
covers. -/
theorem normMapOfCover_zeroAt_iff [IsFinite f] (y : Y) :
    zeroAt (normInvertible f N L) (normInvertible f N L')
        (normMapOfCover f N L L' hL hL' φ) y ↔
      ∃ x : X, f x = y ∧ zeroAt L L' φ x := by
  obtain ⟨c, hy⟩ := Opens.mem_iSup.mp
    (normMapCharts_cover f L L' hL hL' ⊤ (show y ∈ (⊤ : Y.Opens) from trivial))
  obtain ⟨⟨U, s, t⟩, hU⟩ := c
  set a : Γ(X, f ⁻¹ᵁ U) := generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ U) s t
    with hadef
  have ha := generatorCoefficient_spec (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ U) s t
  rw [zeroAt_iff_evaluation_eq_zero _ _ _ U y hy (normGenerator f N L hL U s)
      (normGenerator f N L' hL' U t) (N.app U a)
      (normMapOfCover_generator f N L L' hL hL' φ U s t a ha),
    evaluation_norm_eq_zero_iff_exists_zero_in_fibre f N U a y hy]
  exact ⟨fun ⟨x, hxy, hx⟩ => ⟨x, hxy, (zeroAt_iff_evaluation_eq_zero L L' φ _ x _ s t a ha).mpr hx⟩,
    fun ⟨x, hxy, hx⟩ => ⟨x, hxy, (zeroAt_iff_evaluation_eq_zero L L' φ _ x _ s t a ha).mp hx⟩⟩

end Cover

section Invertible

/-- **The trivializing target cover of Tag 0BUT**, for invertibility in the
`AlgebraicGeometry.SheafOfModules.IsInvertible` spelling of Tag 01CS. This is
`hasTrivializingTargetCover_of_isFinite` composed with
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, the identification of the two
invertibility classes the repository carries. -/
theorem hasTrivializingTargetCover_of_isInvertible (f : X ⟶ Y) [IsFinite f] (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) L] :
    HasTrivializingTargetCover f L :=
  have : IsInvertible X.presheaf
      (structureSheafRing
        X.toRingedSpace).property L :=
    (isInvertible_iff_algebraicGeometry X.presheaf
      (structureSheafRing
        X.toRingedSpace).property L).2 hL
  hasTrivializingTargetCover_of_isFinite f L

variable (f : X ⟶ Y) [IsFinite f] {d : ℕ} (N : MorphismNorm f d) (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) L']
  (φ : L ⟶ L')

/-- **The norm of a map of invertible modules.** A norm `N` of degree `d` on functions along a
finite morphism `f : X ⟶ Y` carries a map `φ : L ⟶ L'` of invertible `𝒪_X`-modules to a map of
the norms of `L` and `L'`. -/
@[stacks 0BCZ "the norm map"]
noncomputable def normMap :
    normInvertible f N.toMorphismNormMap L ⟶ normInvertible f N.toMorphismNormMap L' :=
  normMapOfCover f N.toMorphismNormMap L L' (hasTrivializingTargetCover_of_isInvertible f L)
    (hasTrivializingTargetCover_of_isInvertible f L') φ

/-- **In local frames the norm map is multiplication by the norm of the coefficient.** If `φ`
carries a frame `s` of `L` over `f ⁻¹ᵁ U` to `a` times a frame `t` of `L'` there, then the norm
of `φ` carries the normed frame of `s` to `N(a)` times the normed frame of `t`. This pins the
norm map down rather than merely asserting that some map with the right vanishing locus
exists. -/
@[stacks 0BCZ "local generator formula"]
theorem normMap_generator (U : Y.Opens)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ U))
    (t : GeneratorSections X.toRingedSpace L' (f ⁻¹ᵁ U)) (a : Γ(X, f ⁻¹ᵁ U))
    (ha : φ.val.app (op (f ⁻¹ᵁ U)) s.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ U)))
        (L'.val.obj (op (f ⁻¹ᵁ U))) _ a t.val) :
    (normMap f N L L' φ).val.app (op U)
        (normGenerator f N.toMorphismNormMap L
          (hasTrivializingTargetCover_of_isInvertible f L) U s).val =
      @SMul.smul ((structureSheaf Y.sheaf).obj.obj (op U))
        ((normInvertible f N.toMorphismNormMap L').val.obj (op U)) _ (N.app U a)
        (normGenerator f N.toMorphismNormMap L'
          (hasTrivializingTargetCover_of_isInvertible f L') U t).val :=
  normMapOfCover_generator f N.toMorphismNormMap L L'
    (hasTrivializingTargetCover_of_isInvertible f L)
    (hasTrivializingTargetCover_of_isInvertible f L') φ U s t a ha

/-- **The norm map vanishes at `y` exactly when the original map vanishes at some point of the
fibre over `y`**: the vanishing locus of the norm of `φ` is the image of the vanishing locus
of `φ`. -/
@[stacks 0BCZ "vanishing locus"]
theorem normMap_zeroAt_iff (y : Y) :
    zeroAt (normInvertible f N.toMorphismNormMap L) (normInvertible f N.toMorphismNormMap L')
        (normMap f N L L' φ) y ↔
      ∃ x : X, f x = y ∧ zeroAt L L' φ x :=
  normMapOfCover_zeroAt_iff f N.toMorphismNormMap L L'
    (hasTrivializingTargetCover_of_isInvertible f L)
    (hasTrivializingTargetCover_of_isInvertible f L') φ y

end Invertible

end Stacks.Divisors
