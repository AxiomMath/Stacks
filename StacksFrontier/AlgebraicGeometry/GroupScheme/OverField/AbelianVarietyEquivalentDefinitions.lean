module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyProjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentityComponentGeometric
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Irreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Equivalent definitions of an abelian variety

Let `k` be a field and let `A` be a group scheme over `k`. Remark 0H2U lists three sets of
properties,

* projective, proper,
* geometrically irreducible, irreducible, geometrically connected, connected,
* smooth, geometrically reduced,

and asserts that choosing one property from each set — sixteen choices in all — always
characterizes an abelian variety in the sense of Definition 03RO, namely a group scheme which is
a proper, geometrically integral variety.

The remark's own argument is not sixteen separate proofs. Within each set the properties are
ordered by strength, so the sixteen conjunctions are sandwiched between the strongest choice,
"projective, geometrically irreducible, smooth", and the weakest, "proper, connected,
geometrically reduced". The remark therefore proves two things: that the weakest choice already
forces `A` to be an abelian variety, and that an abelian variety satisfies the strongest choice.
That is the route formalized here.

## Main results

* `AlgebraicGeometry.isAbelianVariety_iff_of_choices` is the remark: for each of the sixteen
  choices of one property from each set, `A` is an abelian variety if and only if it has the
  chosen properties.
* `geometricallyIrreducible_of_isProper_of_connectedSpace_of_geometricallyReduced` (in the
  namespace `AlgebraicGeometry`) is the step the remark isolates: a proper, connected,
  geometrically reduced group scheme over a field is geometrically irreducible.
* `AlgebraicGeometry.isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced`
  is the weakest choice: such a group scheme is an abelian variety.
* `AlgebraicGeometry.isAbelianVariety_of_choices` is the implication from each of the sixteen
  choices at once, the three sets of properties entering as three disjunctions.
* `AlgebraicGeometry.isAbelianVariety_iff_isProper_of_connectedSpace_of_geometricallyReduced`
  turns the weakest choice into an equivalence with Definition 03RO.
* `AlgebraicGeometry.smooth_of_isAbelianVariety` and
  `AlgebraicGeometry.isProjective_of_isAbelianVariety` (Tag 0BFA) are the converse direction, two
  of the three components of the strongest choice; the third, geometric irreducibility, is found
  by instance search, `AlgebraicGeometry.IsAbelianVariety` extending geometric integrality.
  `AlgebraicGeometry.geometricallyConnected_of_isAbelianVariety` is the one weaker option that no
  existing instance draws from them.

## Implementation notes

"Projective" is `AlgebraicGeometry.IsProjective`, the first condition of Tag 01W8, which is the
source's notion. It implies properness by `AlgebraicGeometry.IsProjective.isProper`, the
remark's citation of Tag 01WC, and an abelian variety is projective by Tag 0BFA, which is the
projectivity half of Proposition 03RP that the remark cites for the strongest choice.

"Connected" and "irreducible" are said of the underlying topological space of `A`, and the
geometric versions are Mathlib's `AlgebraicGeometry.GeometricallyConnected` and
`AlgebraicGeometry.GeometricallyIrreducible` of the structure morphism; the remaining options are
`AlgebraicGeometry.IsProper`, `AlgebraicGeometry.Smooth` and
`AlgebraicGeometry.GeometricallyReduced` of the structure morphism.

Geometric irreducibility of a connected group scheme is obtained from Tag 047M, which produces it
for the closed subscheme cut out by the vanishing ideal of an irreducible component containing the
identity. Here the whole space is that component, and its vanishing ideal is the nilradical; the
two private lemmas transport the resulting geometric irreducibility of the reduction along the
universal homeomorphism `A_red ⟶ A`, which is where geometric reducedness of `A` is not needed —
it is needed instead for `AlgebraicGeometry.smooth_of_grpObj`.

## References

* [Stacks Project, Tag 0H2U](https://stacks.math.columbia.edu/tag/0H2U)
* [Stacks Project, Tag 0BFC](https://stacks.math.columbia.edu/tag/0BFC)
* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFA](https://stacks.math.columbia.edu/tag/0BFA)
* [Stacks Project, Tag 0B7Q](https://stacks.math.columbia.edu/tag/0B7Q)
* [Stacks Project, Tag 047M](https://stacks.math.columbia.edu/tag/047M)
* [Stacks Project, Tag 038K](https://stacks.math.columbia.edu/tag/038K)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
-/

public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

open CartesianMonoidalCategory

/-- The reduction of an irreducible group scheme over a field is geometrically irreducible.

This is Tag 047M read at the irreducible component which is the whole space: its vanishing ideal
is the nilradical, so the closed subscheme Tag 047M speaks about is the reduction. -/
@[sga "3 VIA 2.4" "(i), special case", sga "3 VIA 2.6.5" "more general"]
private theorem geometricallyIrreducible_nilradical_of_irreducibleSpace
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IrreducibleSpace G.left] :
    GeometricallyIrreducible (G.left.nilradical.subschemeι ≫ G.hom) := by
  have hG : G = Over.mk G.hom := by
    cases G
    rfl
  let _ : GrpObj (Over.mk G.hom) := hG ▸ (inferInstance : GrpObj G)
  let Z : irreducibleComponents G.left := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    simp⟩
  have h := geometricallyIrreducible_irreducibleComponent_of_identity k G.left G.hom Z
    fun x _ => Set.mem_univ x
  have hZtop :
      (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
        TopologicalSpace.Closeds G.left) = ⊤ := by
    ext x
    simp [Z]
  rwa [hZtop, Scheme.IdealSheafData.vanishingIdeal_top] at h

/-- Geometric irreducibility of the reduction of `X` over `S` transports to `X`: the base change
of `X ×_S Spec K` along `X_red ⟶ X` is a homeomorphism, because `X_red ⟶ X` is a universal
homeomorphism. -/
private alias irreducibleSpace_pullback_of_geometricallyIrreducible_nilradical :=
  AlgebraicGeometry.irreducibleSpace_pullback_of_geometricallyIrreducible_reduction

/-- A proper, connected, geometrically reduced group scheme over a field is geometrically
irreducible.

This is the step the remark isolates, by Tags 0B7Q and 047M: the group scheme is irreducible
because it is connected, hence its reduction is geometrically irreducible, and that transports
back along the universal homeomorphism `A_red ⟶ A`. -/
@[ega "IV 15.6.10" "special case",
  sga "3 IX 5.5" "special case",
  sga "3 VIA 2.4" "(i), special case",
  sga "3 VIA 2.6.5" "(ii), special case"]
theorem geometricallyIrreducible_of_isProper_of_connectedSpace_of_geometricallyReduced
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [ConnectedSpace A.left] [GeometricallyReduced A.hom] :
    GeometricallyIrreducible A.hom := by
  have : IrreducibleSpace A.left := irreducibleSpace_of_connectedSpace A
  have hred := geometricallyIrreducible_nilradical_of_irreducibleSpace k A
  refine ⟨fun K _ g Z _ _ hpull => ?_⟩
  let e : Z ≅ pullback A.hom g := (Over.forget A.left).mapIso hpull.isoOverPullback
  exact e.hom.homeomorph.irreducibleSpace_iff.mpr
    (irreducibleSpace_pullback_of_geometricallyIrreducible_nilradical A.hom hred K g)

/-- The weakest of the sixteen choices of Tag 0H2U: a proper, connected, geometrically reduced
group scheme over a field is an abelian variety.

Geometric irreducibility is the previous result, and together with geometric reducedness it gives
geometric integrality by Tag 038K; properness and geometric integrality are Definition 03RO. -/
@[sga "3 IX 5.5" "special case"]
theorem isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [ConnectedSpace A.left] [GeometricallyReduced A.hom] :
    IsAbelianVariety k A := by
  have : GeometricallyIrreducible A.hom :=
    geometricallyIrreducible_of_isProper_of_connectedSpace_of_geometricallyReduced k A
  have : GeometricallyIntegral A.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible A.hom
  have hIntegral : IsIntegral A.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (f := A.hom)
  have hvariety : IsProperVariety k A.hom := by
    refine (isProperVariety_iff k A.hom).2 ⟨?_, ‹IsProper A.hom›⟩
    exact { toIsIntegral := hIntegral
            toIsSeparated := inferInstance
            toLocallyOfFiniteType := inferInstance
            toQuasiCompact := inferInstance }
  exact { toIsProperVariety := hvariety
          toGeometricallyIntegral := ‹GeometricallyIntegral A.hom› }

/-- The sixteen choices of Tag 0H2U at once, in one direction. Let `A` be a group scheme over a
field `k` which is projective or proper, is geometrically irreducible or irreducible or
geometrically connected or connected, and is smooth or geometrically reduced. Then `A` is an
abelian variety.

Each disjunct reduces to the weakest option of its set: projectivity to properness by Tag 01WC,
each connectedness condition to connectedness of the underlying space, and smoothness to
geometric reducedness by Tag 056T. -/
@[ega "IV 15.6.10" "special case",
  sga "3 IX 5.5" "special case",
  sga "3 VIB 12.3" "sufficient direction"]
theorem isAbelianVariety_of_choices
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    (hcompact : IsProjective A.hom ∨ IsProper A.hom)
    (hconnected : GeometricallyIrreducible A.hom ∨ IrreducibleSpace A.left ∨
      GeometricallyConnected A.hom ∨ ConnectedSpace A.left)
    (hreduced : Smooth A.hom ∨ GeometricallyReduced A.hom) :
    IsAbelianVariety k A := by
  have : IsProper A.hom := hcompact.elim (·.isProper) id
  have : ConnectedSpace A.left := by
    rcases hconnected with _ | _ | _ | _
    · have := GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.hom
      infer_instance
    · infer_instance
    · exact GeometricallyConnected.connectedSpace_of_subsingleton A.hom
    · assumption
  have : GeometricallyReduced A.hom :=
    hreduced.elim (fun _ => geometricallyReduced_of_smooth A.hom) id
  exact isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced k A

/-- An abelian variety over a field is smooth over that field.

This is the third component of the strongest of the sixteen choices, and Tag 0BFC: an abelian
variety is a group scheme, locally of finite type, and geometrically reduced because it is
geometrically integral. -/
@[ega "IV 15.6.10" "(iii), special case",
  sga "3 VIB 7.8" "special case",
  sga "3 XV 4.6" "special case",
  sga "7 VIII 4.1" "special case"]
theorem smooth_of_isAbelianVariety
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] : Smooth A.hom :=
  have : GrpObj (Over.mk A.hom) := inferInstanceAs (GrpObj A)
  smooth_of_grpObj A.hom

/-- For a group scheme over a field, being an abelian variety is equivalent to the weakest of the
sixteen choices of Tag 0H2U: proper, connected, and geometrically reduced. -/
@[sga "3 IX 5.5" "special case"]
theorem isAbelianVariety_iff_isProper_of_connectedSpace_of_geometricallyReduced
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    IsAbelianVariety k A ↔
      IsProper A.hom ∧ ConnectedSpace A.left ∧ GeometricallyReduced A.hom := by
  refine ⟨fun h => ?_, fun ⟨_, _, _⟩ => ?_⟩
  · have := GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.hom
    exact ⟨h.toIsProper, inferInstance, inferInstance⟩
  · exact isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced k A

/-- An abelian variety over a field is geometrically connected: every base change to a field is
irreducible, hence connected. -/
theorem geometricallyConnected_of_isAbelianVariety
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] : GeometricallyConnected A.hom :=
  ⟨fun _ _ y Z fst snd h ↦ @IrreducibleSpace.connectedSpace Z _
    ((inferInstance : GeometricallyIrreducible A.hom).geometrically_irreducibleSpace y fst snd h)⟩

/-- **Stacks Project, Tag 0H2U.** Let `k` be a field and `A` a group scheme over `k`. Pick one
property from each of the three sets

* projective, proper;
* geometrically irreducible, irreducible, geometrically connected, connected;
* smooth, geometrically reduced.

Then `A` is an abelian variety if and only if it has the three chosen properties over `k`; so the
sixteen choices are sixteen equivalent definitions of an abelian variety. The choice "proper,
geometrically irreducible, geometrically reduced" recovers Definition 03RO.

Every choice implies the weakest one, "proper, connected, geometrically reduced", which makes `A`
an abelian variety (`AlgebraicGeometry.isAbelianVariety_of_choices`); conversely an abelian
variety is projective by Tag 0BFA, smooth by Tag 0BFC and geometrically irreducible, which is the
strongest choice and implies every other. -/
@[stacks 0H2U,
  ega "IV 15.6.10" "special case",
  sga "3 VIB 12.3" "more general",
  sga "3 VIB 7.8" "special case",
  sga "3 XV 4.6" "special case",
  sga "7 VIII 4.1" "Proper group schemes"]
theorem isAbelianVariety_iff_of_choices
    (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    ∀ P₁ ∈ [IsProjective A.hom, IsProper A.hom],
    ∀ P₂ ∈ [GeometricallyIrreducible A.hom, IrreducibleSpace A.left,
      GeometricallyConnected A.hom, ConnectedSpace A.left],
    ∀ P₃ ∈ [Smooth A.hom, GeometricallyReduced A.hom],
      (IsAbelianVariety k A ↔ P₁ ∧ P₂ ∧ P₃) := by
  have hconv : IsAbelianVariety k A →
      (IsProjective A.hom ∧ IsProper A.hom) ∧
        (GeometricallyIrreducible A.hom ∧ IrreducibleSpace A.left ∧
          GeometricallyConnected A.hom ∧ ConnectedSpace A.left) ∧
        (Smooth A.hom ∧ GeometricallyReduced A.hom) := by
    intro h
    have hirr : IrreducibleSpace A.left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.hom
    exact ⟨⟨isProjective_of_isAbelianVariety k A, h.toIsProper⟩,
      ⟨inferInstance, hirr,
        geometricallyConnected_of_isAbelianVariety k A, inferInstance⟩,
      ⟨smooth_of_isAbelianVariety k A, inferInstance⟩⟩
  intro P₁ h₁ P₂ h₂ P₃ h₃
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂ h₃
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl | rfl | rfl <;>
    rcases h₃ with rfl | rfl <;>
    exact ⟨fun h => by have := hconv h; tauto,
      fun h => isAbelianVariety_of_choices k A (by tauto) (by tauto) (by tauto)⟩

-- Tag 0BFC is the smoothness of an abelian variety over a field, which is
-- `AlgebraicGeometry.smooth_of_isAbelianVariety` above.
add_to_stacks 0BFC AlgebraicGeometry.smooth_of_isAbelianVariety

end AlgebraicGeometry

end
