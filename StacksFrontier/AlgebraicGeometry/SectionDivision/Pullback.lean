module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.SectionDivision.Basic

/-!
# The ratio of two pulled-back sections is the pullback of the ratio

Let `φ : X ⟶ Y` be a morphism of schemes, `L` an invertible `𝒪_Y`-module and `s`, `t` two global
sections of `L`. Over the nonvanishing locus `Y_s` the quotient `t / s`
(`Stacks.SheafOfModules.divBySection`) is a section of `𝒪_Y`, and `φ` carries it to a section of
`𝒪_X` over `φ⁻¹(Y_s)`. On the other side, `s` and `t` have pullbacks
(`Stacks.SheafOfModules.modulePullbackSection`), global sections of the invertible module `φ^*L`
(Tag 0B8L), and `φ⁻¹(Y_s)` is the nonvanishing locus of `φ^*s` (Tag 0H78,
`Stacks.SheafOfModules.preimage_nonvanishingOpen`), so `(φ^*t) / (φ^*s)` is defined there too.
This file proves the two agree:

  `(φ^*t) / (φ^*s) = φ^♯ (t / s)`   on `φ⁻¹(Y_s)`, and more generally on any `V ⊆ φ⁻¹(Y_s)`.

This is the computation that makes the chart description of a morphism into projective space
(Tag 01NA, Tag 01NE) compatible with base change: the homogeneous coordinates of a composite
`X ⟶ Y ⟶ ℙⁿ` are the pullbacks of those of `Y ⟶ ℙⁿ`, so their ratios are the pullbacks of the
ratios.

## Main results

* `Stacks.RingedSpace.sharp_eq_app`: for a morphism of schemes, `Stacks.RingedSpace.sharp` — the
  action of the structure morphism on a scalar, as the pullback adjunction uses it — is
  `AlgebraicGeometry.Scheme.Hom.app`. This holds by `rfl` and is the bridge between the
  ringed-space pullback API and the scheme API.
* `Stacks.SheafOfModules.modulePullbackSection_eval_preimage`: the pullback of a global section
  evaluates over a preimage open `f⁻¹U` to the pullback-unit image of the section over `U`. This
  is `Stacks.SheafOfModules.modulePullbackSection_eval_top` moved down from `⊤`.
* `Stacks.SheafOfModules.divBySection_modulePullbackSection_preimage`: **the ratio of the
  pullbacks is the pullback of the ratio**, over `φ⁻¹(Y_s)`.
* `Stacks.SheafOfModules.divBySection_modulePullbackSection` and
  `Stacks.SheafOfModules.divBySection_modulePullbackSection_map`: the same over any open
  `V ⊆ φ⁻¹(Y_s)`, with the right-hand side written as `AlgebraicGeometry.Scheme.Hom.appLE` and,
  definitionally equivalently, as pullback along `φ` followed by restriction.

## Implementation notes

The proof is the uniqueness clause `Stacks.SheafOfModules.divBySection_eq_of_smul_eq` applied to
an explicit witness, like every other statement in
`StacksFrontier/AlgebraicGeometry/SectionDivision/Basic.lean`. The witness is `φ^♯(t/s)`, and the
single piece of input is the semilinearity of the pullback unit,
`Stacks.RingedSpace.pullbackUnit_smul`: applying the unit to `(t/s) · s|_{Y_s} = t|_{Y_s}` turns
the scalar `t/s` into `φ^♯(t/s)` and the two sections into the pullback sections, which is exactly
the defining property of `(φ^*t)/(φ^*s)`.

Three spelling frictions are worth recording, since each defeats a rewrite.

* `Stacks.RingedSpace.sharp` and `AlgebraicGeometry.Scheme.Hom.app` are the same function, but
  only up to `rfl`; `sharp_eq_app` is stated so that the `•` produced by `pullbackUnit_smul` can
  be matched against a goal written in the scheme API.
* `structureSheafRing` and
  `structureSheafRing` are also equal
  only up to unfolding a semireducible definition, so a scalar multiplication whose ring is
  spelled one way does not unify with the `Module` instance spelled the other way. Hence no
  statement below writes a `•` of its own: the scalar multiplications all arrive inside
  `pullbackUnit_smul` and `Stacks.SheafOfModules.smul_divBySection`, which are combined by
  `congrArg` and `Eq.trans` rather than by `rw`. For the same reason
  `Stacks.SheafOfModules.secRestr_sections_eval` is not usable as a rewrite rule here and
  `PresheafOfModules.sections_property` is used directly.
* `(RingedSpaceModuleAdjunction.opensMap f).obj ⊤` and `⊤` are definitionally but not
  syntactically equal, so the two restriction morphisms `op ⊤ ⟶ op (f⁻¹U)` appearing in
  `modulePullbackSection_eval_preimage` are identified by `Subsingleton.elim` on a hom-set of a
  poset, as in `modulePullbackSection_eval_top`.

No `@[stacks]` attribute is claimed: the Stacks Project uses this computation inside the proof of
Tag 01N8 without stating it, so there is no tag whose covering set these declarations form.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace (structureRingSheaf sharp pullbackUnit pullbackUnit_smul
  pullbackUnit_restrict)

universe u

namespace Stacks.RingedSpace

/-- **The structure morphism of a morphism of schemes, as the pullback adjunction uses it.**
`Stacks.RingedSpace.sharp` of the underlying morphism of ringed spaces is
`AlgebraicGeometry.Scheme.Hom.app`. This holds by `rfl`, and is the bridge that lets the
semilinearity of `Stacks.RingedSpace.pullbackUnit` be read in the scheme API. -/
theorem sharp_eq_app {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    sharp φ.toLRSHom.toShHom (op U) r = (φ.app U).hom r := rfl

end Stacks.RingedSpace

namespace Stacks.SheafOfModules

section Preimage

variable {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
  (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- **The pullback of a global section, evaluated over a preimage open.** Over `f⁻¹U` the
pullback of `s` is the image of `s|_U` under the unit of `f^* ⊣ f_*`. This is
`Stacks.SheafOfModules.modulePullbackSection_eval_top` transported from `⊤` down to `U`, using
`Stacks.RingedSpace.pullbackUnit_restrict`. -/
theorem modulePullbackSection_eval_preimage (s : L.sections) (U : (Opens X.carrier)ᵒᵖ) :
    (modulePullbackSection f L s).eval ((opensMap f.toShHom).op.obj U) =
      pullbackUnit f.toShHom L U (s.eval U) := by
  have hs : L.val.restrictₛₗ ((homOfLE (le_top : U.unop ≤ ⊤)).op) (s.eval (op ⊤))
      = s.eval U := PresheafOfModules.sections_property s _
  have hunit := pullbackUnit_restrict f.toShHom L ((homOfLE (le_top : U.unop ≤ ⊤)).op)
    (s.eval (op ⊤))
  rw [hs] at hunit
  change ((modulePullback f.toShHom).obj L).val.map
      (homOfLE (le_top : ((opensMap f.toShHom).obj U.unop) ≤ ⊤)).op
      (pullbackUnit f.toShHom L (op ⊤) (s.eval (op ⊤))) = _
  rw [show (homOfLE (le_top : ((opensMap f.toShHom).obj U.unop) ≤ ⊤)).op
      = (opensMap f.toShHom).op.map ((homOfLE (le_top : U.unop ≤ ⊤)).op) from
    Subsingleton.elim _ _]
  exact hunit

end Preimage

section Scheme

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) (L : Y.Modules)
  [hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L]

/-- **The ratio of two pulled-back sections is the pullback of the ratio**, over the preimage of
the nonvanishing locus: `(φ^*t) / (φ^*s) = φ^♯ (t / s)` on `φ⁻¹(Y_s)`.

The pullback module is invertible by Tag 0B8L and `φ⁻¹(Y_s)` is the nonvanishing locus of `φ^*s`
by Tag 0H78, so the left-hand side is defined; the proof is the uniqueness clause
`Stacks.SheafOfModules.divBySection_eq_of_smul_eq` applied to the witness `φ^♯(t/s)`, which works
because the unit of `φ^* ⊣ φ_*` is semilinear over `φ^♯`
(`Stacks.RingedSpace.pullbackUnit_smul`). -/
theorem divBySection_modulePullbackSection_preimage (s t : L.sections) :
    letI : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
        ((modulePullback φ.toLRSHom.toShHom).obj L) :=
      @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
        φ.toLRSHom.toShHom L hL
    divBySection ((modulePullback φ.toLRSHom.toShHom).obj L)
        (modulePullbackSection φ.toLRSHom L s)
        (le_of_eq (preimage_nonvanishingOpen φ L s))
        ((modulePullbackSection φ.toLRSHom L t).eval
          (op (φ ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) L s)))
      = (φ.app (nonvanishingOpen (X := Y.toRingedSpace) L s)).hom
          (divBySection L s le_rfl
            (t.eval (op (nonvanishingOpen (X := Y.toRingedSpace) L s)))) := by
  have : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
      ((modulePullback φ.toLRSHom.toShHom).obj L) :=
    @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
      φ.toLRSHom.toShHom L hL
  have hsmul := pullbackUnit_smul φ.toLRSHom.toShHom L
    (op (nonvanishingOpen (X := Y.toRingedSpace) L s))
    (divBySection L s le_rfl
      (t.eval (op (nonvanishingOpen (X := Y.toRingedSpace) L s))))
    (s.eval (op (nonvanishingOpen (X := Y.toRingedSpace) L s)))
  have hnum := congrArg
    (pullbackUnit φ.toLRSHom.toShHom L (op (nonvanishingOpen (X := Y.toRingedSpace) L s)))
    (smul_divBySection L s (le_rfl :
      nonvanishingOpen (X := Y.toRingedSpace) L s ≤ nonvanishingOpen (X := Y.toRingedSpace) L s)
      (t.eval (op (nonvanishingOpen (X := Y.toRingedSpace) L s))))
  have key := hsmul.symm.trans hnum
  rw [← modulePullbackSection_eval_preimage φ.toLRSHom L s
      (op (nonvanishingOpen (X := Y.toRingedSpace) L s)),
    ← modulePullbackSection_eval_preimage φ.toLRSHom L t
      (op (nonvanishingOpen (X := Y.toRingedSpace) L s))] at key
  exact divBySection_eq_of_smul_eq _ _ _ key

/-- **The ratio of two pulled-back sections is the pullback of the ratio**, over any open
contained in the preimage of the nonvanishing locus. The right-hand side is
`AlgebraicGeometry.Scheme.Hom.appLE`, that is, `t / s` pulled back along `φ` and restricted
to `V`.

This is `Stacks.SheafOfModules.divBySection_modulePullbackSection_preimage` together with
`Stacks.SheafOfModules.map_divBySection`, the compatibility of the quotient with restriction. -/
theorem divBySection_modulePullbackSection (s t : L.sections) {V : X.Opens}
    (hV : V ≤ φ ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) L s) :
    letI : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
        ((modulePullback φ.toLRSHom.toShHom).obj L) :=
      @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
        φ.toLRSHom.toShHom L hL
    divBySection ((modulePullback φ.toLRSHom.toShHom).obj L)
        (modulePullbackSection φ.toLRSHom L s)
        (hV.trans (le_of_eq (preimage_nonvanishingOpen φ L s)))
        ((modulePullbackSection φ.toLRSHom L t).eval (op V))
      = (φ.appLE (nonvanishingOpen (X := Y.toRingedSpace) L s) V hV).hom
          (divBySection L s le_rfl
            (t.eval (op (nonvanishingOpen (X := Y.toRingedSpace) L s)))) := by
  have : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
      ((modulePullback φ.toLRSHom.toShHom).obj L) :=
    @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
      φ.toLRSHom.toShHom L hL
  have hres := map_divBySection ((modulePullback φ.toLRSHom.toShHom).obj L)
    (modulePullbackSection φ.toLRSHom L s) hV
    (le_of_eq (preimage_nonvanishingOpen φ L s))
    ((modulePullbackSection φ.toLRSHom L t).eval
      (op (φ ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) L s)))
  have hrestr : ((((modulePullback φ.toLRSHom.toShHom).obj L).val).restrictₛₗ ((homOfLE hV).op))
        ((modulePullbackSection φ.toLRSHom L t).eval
          (op (φ ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) L s)))
      = (modulePullbackSection φ.toLRSHom L t).eval (op V) :=
    PresheafOfModules.sections_property (modulePullbackSection φ.toLRSHom L t)
      (homOfLE hV).op
  exact (congrArg (divBySection ((modulePullback φ.toLRSHom.toShHom).obj L)
        (modulePullbackSection φ.toLRSHom L s)
        (hV.trans (le_of_eq (preimage_nonvanishingOpen φ L s)))) hrestr).symm.trans
      (hres.symm.trans (congrArg (X.presheaf.map (homOfLE hV).op).hom
        (divBySection_modulePullbackSection_preimage φ L s t)))

/-- `Stacks.SheafOfModules.divBySection_modulePullbackSection` with the right-hand side written
out as "pull back along `φ`, then restrict", which is what
`AlgebraicGeometry.Scheme.Hom.appLE` is by definition. -/
theorem divBySection_modulePullbackSection_map (s t : L.sections) {V : X.Opens}
    (hV : V ≤ φ ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) L s) :
    letI : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
        ((modulePullback φ.toLRSHom.toShHom).obj L) :=
      @Stacks.RingedSpace.isInvertible_modulePullback X.toRingedSpace Y.toRingedSpace
        φ.toLRSHom.toShHom L hL
    divBySection ((modulePullback φ.toLRSHom.toShHom).obj L)
        (modulePullbackSection φ.toLRSHom L s)
        (hV.trans (le_of_eq (preimage_nonvanishingOpen φ L s)))
        ((modulePullbackSection φ.toLRSHom L t).eval (op V))
      = (X.presheaf.map (homOfLE hV).op).hom
          ((φ.app (nonvanishingOpen (X := Y.toRingedSpace) L s)).hom
            (divBySection L s le_rfl
              (t.eval (op (nonvanishingOpen (X := Y.toRingedSpace) L s))))) :=
  divBySection_modulePullbackSection φ L s t hV

end Scheme

end Stacks.SheafOfModules

end
