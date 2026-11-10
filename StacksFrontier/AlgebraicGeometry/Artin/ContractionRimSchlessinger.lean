module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionOnePoint
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionOpenPart
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FunctorForm
import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionComparison
import StacksFrontier.AlgebraicGeometry.FormalSpace.RimSchlessinger
import StacksFrontier.Deformation.Artin.RimSchlessinger.AlgebraicSpaceFunctor

/-!
# Artin's contraction functor satisfies the Rim–Schlessinger condition

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`, let
`F` be Artin's functor of Stacks 0GHA, `AlgebraicGeometry.Artin.contractionFunctor`. **Stacks
0GI6** says that `F` satisfies the Rim–Schlessinger condition (RS), in the form of axiom [2] of
Section 0GE6, `AlgebraicGeometry.LocallyNoetherianOver.SatisfiesRS`.

The proof is the source's. On the spectrum `V` of an Artinian local ring an element
`(Z, u', x̂)` of `F(V)` has `Z = ∅` or `Z = V`. In the first case it is the element
`AlgebraicGeometry.Artin.ContractionSituation.emptyTriple` of the point `u' : V ⟶ U'`, in the
second the element `AlgebraicGeometry.Artin.ContractionSituation.tripleOfSection` of the point
`x̂ : V ⟶ W`; so `F(V) = U'(V) ⨿ W(V)`, compatibly with restriction. The two kinds cannot be
identified after restriction to a nonempty scheme, so a compatible pair over the two middle
corners of an (RS) square is a compatible pair of points of `U'` or a compatible pair of points
of `W`, and (RS) for `F` follows from (RS) for `U'` and for `W`:

* `U'` is an algebraic space, an open subspace of `X'`, and satisfies (RS) by Stacks 07WQ
  (`Deformation.Artin.satisfiesRSFunctor_of_isAlgebraicSpace`);
* `W` is a formal algebraic space and satisfies (RS) by
  `AlgebraicGeometry.FormalSpace.satisfiesRSFunctor_of_isFormalAlgebraicSpace`.

## Main results

* `AlgebraicGeometry.Artin.contractionFunctor_satisfiesRS`: **Stacks 0GI6**.

## Implementation notes

The source reduces (RS) for `W` to Stacks 07WQ for the algebraic spaces `W_n` of a presentation
`W = colim W_n` (Stacks 0GHM). The library has Stacks 0GHM only for a Noetherian affine formal
algebraic space, and (RS) for `W` is instead proved directly from an affine formal étale atlas;
see the implementation notes of `StacksFrontier.AlgebraicGeometry.FormalSpace.RimSchlessinger`.

## References

* [Stacks Project, Tag 0GI6](https://stacks.math.columbia.edu/tag/0GI6)
* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}

/-- For a triple with `Z = ∅`, the point of `U'` over `V` given by its second component
`u' : V ∖ Z ⟶ U'` at the identity of `V`. -/
def Triple.uPoint (t : Triple c V) (h : t.Z = ∅) : c.U'.toFunctor.obj (op V) :=
  t.u.app (op V) ⟨𝟙 V, t.id_mem_openSubspace h⟩

/-- The point of `U'` of a triple with `Z = ∅` is compatible with restriction. -/
theorem Triple.uPoint_mapTriple {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (h : t.Z = ∅) (h' : (mapTriple c φ t).Z = ∅) :
    (mapTriple c φ t).uPoint h' = c.U'.toFunctor.map φ.op (t.uPoint h) :=
  Subtype.ext (t.uValue_mapTriple φ h h')

/-- The point of `U'` of a triple with `Z = ∅` depends only on the triple. -/
theorem Triple.uPoint_congr {t t' : Triple c V} (e : t = t') (h : t.Z = ∅) (h' : t'.Z = ∅) :
    t.uPoint h = t'.uPoint h' := by
  subst e; rfl

/-- The point of `U'` of the triple `(∅, u, ∅ ⟶ W)` of `u : V ⟶ U'` is `u`. -/
theorem uPoint_emptyTriple (u : yoneda.obj V ⟶ c.U'.toFunctor) (h : (c.emptyTriple V u).Z = ∅) :
    (c.emptyTriple V u).uPoint h = yonedaEquiv u :=
  rfl

/-- On a nonempty scheme no two equal triples have closed subsets `∅` and `|V|`. -/
theorem Triple.Z_ne_of_nonempty [Nonempty ((BigFppfOver.toScheme B S hS).obj V)]
    {t t' : Triple c V} (e : t = t') (h : t.Z = ∅) (h' : t'.Z = Set.univ) : False := by
  obtain ⟨y⟩ := ‹Nonempty ((BigFppfOver.toScheme B S hS).obj V)›
  subst e
  have hy : (Space.pointsEquivScheme B S hS V).symm y ∈ t.Z := h' ▸ Set.mem_univ _
  rw [h] at hy
  exact hy

end ContractionSituation

open ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying scheme of an object of the site whose underlying scheme is affine with local
ring of global sections is nonempty. -/
theorem nonempty_toScheme_of_isLocalRing (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] :
    Nonempty ((BigFppfOver.toScheme B S hS).obj V) :=
  ⟨(Scheme.homeoOfIso ((BigFppfOver.toScheme B S hS).obj V).isoSpec).symm
    (IsLocalRing.closedPoint _)⟩

/-- A triple with `Z = ∅` is the restriction of the triple of a point `e` of `U'` as soon as `e`
restricts to the point of `U'` of the triple. -/
private theorem mapTriple_emptyTriple_eq (c : ContractionSituation B S hS)
    {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (e : c.U'.toFunctor.obj (op V₁))
    (t : Triple c V₂) (ht : t.Z = ∅) (h : c.U'.toFunctor.map φ.op e = t.uPoint ht) :
    mapTriple c φ (c.emptyTriple V₁ (yonedaEquiv.symm e)) = t := by
  rw [← emptyTriple_comp]
  refine Triple.ext_of_Z_eq_empty (emptyTriple_Z c _ _) ht
    (congrArg Subtype.val (?_ : Triple.uPoint _ (emptyTriple_Z c _ _) = t.uPoint ht))
  rw [uPoint_emptyTriple, ← h, show yoneda.map φ ≫ yonedaEquiv.symm e =
    yonedaEquiv.symm (c.U'.toFunctor.map φ.op e) from (yonedaEquiv_symm_map φ.op e).symm,
    Equiv.apply_symm_apply]

/-- A triple with `Z = Set.univ` is the restriction of the triple of a section `e` of `W` as soon
as `e` restricts to the section of `W` of the triple. -/
private theorem mapTriple_tripleOfSection_eq (c : ContractionSituation B S hS)
    {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (e : c.W.obj.obj (op V₁))
    (t : Triple c V₂) (ht : t.Z = Set.univ) (h : c.W.obj.map φ.op e = wSection c t ht) :
    mapTriple c φ (tripleOfSection c V₁ e) = t := by
  have hZ := Triple.mapTriple_Z_eq_univ c φ (tripleOfSection c V₁ e) rfl
  refine Triple.eq_of_Z_eq_univ c _ _ hZ ht ?_
  rw [wSection_mapTriple c φ _ rfl hZ, wSection_tripleOfSection, h]

/-- Two triples with `Z = ∅` with the same restriction have the same restricted point of `U'`. -/
private theorem map_uPoint_eq_of_mapTriple_eq (c : ContractionSituation B S hS)
    {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) {t t' : Triple c V₁}
    (e : mapTriple c φ t = mapTriple c φ t') (ht : t.Z = ∅) (ht' : t'.Z = ∅) :
    c.U'.toFunctor.map φ.op (t.uPoint ht) = c.U'.toFunctor.map φ.op (t'.uPoint ht') := by
  rw [← t.uPoint_mapTriple φ ht (Triple.mapTriple_Z_eq_empty c φ t ht),
    ← t'.uPoint_mapTriple φ ht' (Triple.mapTriple_Z_eq_empty c φ t' ht')]
  exact Triple.uPoint_congr e _ _

/-- Two triples with `Z = Set.univ` with the same restriction have the same restricted section of
`W`. -/
private theorem map_wSection_eq_of_mapTriple_eq (c : ContractionSituation B S hS)
    {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) {t t' : Triple c V₁}
    (e : mapTriple c φ t = mapTriple c φ t') (ht : t.Z = Set.univ) (ht' : t'.Z = Set.univ) :
    c.W.obj.map φ.op (wSection c t ht) = c.W.obj.map φ.op (wSection c t' ht') := by
  rw [← wSection_mapTriple c φ t ht (Triple.mapTriple_Z_eq_univ c φ t ht),
    ← wSection_mapTriple c φ t' ht' (Triple.mapTriple_Z_eq_univ c φ t' ht')]
  exact wSection_congr c e _ _

/-- **Stacks 0GI6.** In the situation of Stacks 0GH8, Artin's functor `F` of Stacks 0GHA
satisfies the Rim–Schlessinger condition (RS): for every pushout `Y' = Y ⨿_X X'` of spectra of
Artinian local rings of finite type over `S` along a closed immersion `X ⟶ X'`, every pair of
elements of `F` over `Y` and `X'` with the same restriction to `X` is the pair of restrictions of
exactly one element of `F(Y')`. -/
@[stacks 0GI6]
theorem contractionFunctor_satisfiesRS (c : ContractionSituation B S hS) :
    LocallyNoetherianOver.SatisfiesRS B S hS (contractionFunctor c) := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo a b hab
  change Triple c Y.obj at a
  change Triple c X'.obj at b
  change mapTriple c j.hom a = mapTriple c i.hom b at hab
  change ∃! t : Triple c Y'.obj, mapTriple c j'.hom t = a ∧ mapTriple c i'.hom t = b
  let T := BigFppfOver.toScheme B S hS
  have w' : i.hom ≫ i'.hom = j.hom ≫ j'.hom := congrArg InducedCategory.Hom.hom w
  -- condition (RS) for `U'` and for `W`, at the square
  have hU' := Deformation.Artin.satisfiesRSFunctor_of_isAlgebraicSpace c.isOpenSubspace_U'.1
    i.hom j.hom i'.hom j'.hom w' hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  have hW := FormalSpace.satisfiesRSFunctor_of_isFormalAlgebraicSpace c.isLocallyNoetherian_W.1
    i.hom j.hom i'.hom j'.hom w' hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  -- the four corners have one point, the first one at least one
  have : IsAffine (T.obj X.obj) := hX.1
  have : IsAffine (T.obj X'.obj) := hX'.1
  have : IsAffine (T.obj Y.obj) := hY.1
  have : IsAffine (T.obj Y'.obj) := hY'.1
  have : IsLocalRing Γ(T.obj X.obj, ⊤) := hX.2.1
  have : IsLocalRing Γ(T.obj X'.obj, ⊤) := hX'.2.1
  have : IsLocalRing Γ(T.obj Y.obj, ⊤) := hY.2.1
  have : IsLocalRing Γ(T.obj Y'.obj, ⊤) := hY'.2.1
  have : IsArtinianRing Γ(T.obj X'.obj, ⊤) := hX'.2.2
  have : IsArtinianRing Γ(T.obj Y.obj, ⊤) := hY.2.2
  have : IsArtinianRing Γ(T.obj Y'.obj, ⊤) := hY'.2.2
  have : Subsingleton (T.obj X'.obj) :=
    FormalSpace.subsingleton_of_isArtinianRing_of_isLocalRing (T.obj X'.obj)
  have : Subsingleton (T.obj Y.obj) :=
    FormalSpace.subsingleton_of_isArtinianRing_of_isLocalRing (T.obj Y.obj)
  have : Subsingleton (T.obj Y'.obj) :=
    FormalSpace.subsingleton_of_isArtinianRing_of_isLocalRing (T.obj Y'.obj)
  have := nonempty_toScheme_of_isLocalRing X.obj
  have := nonempty_toScheme_of_isLocalRing Y.obj
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases a.Z_eq_empty_or_eq_univ with ha | ha
    · -- `a` and `b` are points of `U'`
      have hjA := Triple.mapTriple_Z_eq_empty c j.hom a ha
      have hb : b.Z = ∅ := (b.Z_eq_empty_or_eq_univ).resolve_right fun hb =>
        Triple.Z_ne_of_nonempty hab hjA (Triple.mapTriple_Z_eq_univ c i.hom b hb)
      have hiB := Triple.mapTriple_Z_eq_empty c i.hom b hb
      obtain ⟨e, ⟨he₁, he₂⟩, -⟩ := hU' (a.uPoint ha) (b.uPoint hb) (by
        rw [← a.uPoint_mapTriple j.hom ha hjA, ← b.uPoint_mapTriple i.hom hb hiB]
        exact Triple.uPoint_congr hab hjA hiB)
      exact ⟨c.emptyTriple Y'.obj (yonedaEquiv.symm e),
        mapTriple_emptyTriple_eq c _ e a ha he₁, mapTriple_emptyTriple_eq c _ e b hb he₂⟩
    · -- `a` and `b` are points of `W`
      have hjA := Triple.mapTriple_Z_eq_univ c j.hom a ha
      have hb : b.Z = Set.univ := (b.Z_eq_empty_or_eq_univ).resolve_left fun hb =>
        Triple.Z_ne_of_nonempty hab.symm (Triple.mapTriple_Z_eq_empty c i.hom b hb) hjA
      have hiB := Triple.mapTriple_Z_eq_univ c i.hom b hb
      obtain ⟨e, ⟨he₁, he₂⟩, -⟩ := hW (wSection c a ha) (wSection c b hb) (by
        rw [← wSection_mapTriple c j.hom a ha hjA, ← wSection_mapTriple c i.hom b hb hiB]
        exact wSection_congr c hab hjA hiB)
      exact ⟨tripleOfSection c Y'.obj e,
        mapTriple_tripleOfSection_eq c _ e a ha he₁, mapTriple_tripleOfSection_eq c _ e b hb he₂⟩
  · rintro t t' ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩
    have e₁ := h₁.trans h₁'.symm
    have e₂ := h₂.trans h₂'.symm
    rcases t.Z_eq_empty_or_eq_univ with ht | ht <;> rcases t'.Z_eq_empty_or_eq_univ with ht' | ht'
    · have key := (hU' _ _ (by
        rw [← types_comp_apply (c.U'.toFunctor.map _) (c.U'.toFunctor.map _),
          ← types_comp_apply (c.U'.toFunctor.map _) (c.U'.toFunctor.map _),
          ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, w'])).unique
        (y₁ := t.uPoint ht) (y₂ := t'.uPoint ht') ⟨rfl, rfl⟩
        ⟨(map_uPoint_eq_of_mapTriple_eq c j'.hom e₁ ht ht').symm,
          (map_uPoint_eq_of_mapTriple_eq c i'.hom e₂ ht ht').symm⟩
      exact Triple.ext_of_Z_eq_empty ht ht' (congrArg Subtype.val key)
    · exact (Triple.Z_ne_of_nonempty e₁ (Triple.mapTriple_Z_eq_empty c j'.hom t ht)
        (Triple.mapTriple_Z_eq_univ c j'.hom t' ht')).elim
    · exact (Triple.Z_ne_of_nonempty e₁.symm (Triple.mapTriple_Z_eq_empty c j'.hom t' ht')
        (Triple.mapTriple_Z_eq_univ c j'.hom t ht)).elim
    · have key := (hW _ _ (by
        rw [← types_comp_apply (c.W.obj.map _) (c.W.obj.map _),
          ← types_comp_apply (c.W.obj.map _) (c.W.obj.map _),
          ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, w'])).unique
        (y₁ := wSection c t ht) (y₂ := wSection c t' ht') ⟨rfl, rfl⟩
        ⟨(map_wSection_eq_of_mapTriple_eq c j'.hom e₁ ht ht').symm,
          (map_wSection_eq_of_mapTriple_eq c i'.hom e₂ ht ht').symm⟩
      exact Triple.eq_of_Z_eq_univ c t t' ht ht' key

end AlgebraicGeometry.Artin
