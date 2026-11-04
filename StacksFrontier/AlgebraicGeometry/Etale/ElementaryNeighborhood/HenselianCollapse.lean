module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.TFAE

/-!
# An elementary étale neighbourhood of a henselian local scheme collapses

Over a henselian base an elementary étale neighbourhood carries no information: if `S` is the
spectrum of a henselian local ring, pointed at its closed point, and `f : X ⟶ S` is étale with
`x ∈ X` lying over that point and inducing an isomorphism on residue fields, then the local
scheme of `X` at `x` is the base itself, in the precise sense that

`X.fromSpecStalk x ≫ f : Spec 𝒪_{X, x} ⟶ S`

is an isomorphism. This is what makes Stacks 05MF usable on a henselian base: 05MF
(`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finiteType`) produces
free sections only after base change to `Spec 𝒪_{S', s'}` for an elementary étale neighbourhood
`(S', s')`, and over a henselian base that base change is an isomorphism, so the free sections
live on the original scheme. The proof of Stacks 05U7 uses exactly this step.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_section_formallyUnramified`: a section of a formally
  unramified morphism locally of finite type is an open immersion.
* `AlgebraicGeometry.isIso_fromSpecStalk_comp_of_henselian`: the collapse, for a bare étale
  morphism.
* `AlgebraicGeometry.EtaleNeighborhood.isIso_fromSpecStalk_comp_toBase_of_henselian`: the
  collapse for an elementary étale neighbourhood, which is the form Stacks 05MF produces.

## Implementation notes

The section is produced by Stacks 05KS: a henselian local ring is its own henselization, so the
colimit of the global sections of the elementary étale neighbourhoods
(`AlgebraicGeometry.isColimit_globalSections`) has `𝒪_{S, s}` itself as its vertex, and the leg
at the neighbourhood `(X, x)` is a local retraction `ρ : 𝒪_{X, x} → 𝒪_{S, s}` of the stalk map.
That `𝒪_{S,s}` is its own henselization is checked through
`IsLocalRing.IsHenselization.of_ind_etale`, the identity being ind-étale.

The retraction gives `β : Spec 𝒪_{S, s} ⟶ X` over `S`, hence — once `Spec 𝒪_{S,s} ⟶ S` is an
isomorphism, which is the hypothesis `IsIso (S.fromSpecStalk s)` — a genuine section
`σ : S ⟶ X` of `f`. A section of an étale morphism is an open immersion
(`isOpenImmersion_of_section_formallyUnramified`, obtained by exhibiting `σ` as a base change of
the diagonal of `f`, which is an open immersion because `f` is formally unramified). Open
immersions are isomorphisms on stalks, which forces `f.stalkMap x` to be an isomorphism, and the
claim follows from `Scheme.SpecMap_stalkMap_fromSpecStalk`.

The two hypotheses `IsIso (S.fromSpecStalk (f x))` and `HenselianLocalRing (S.presheaf.stalk
(f x))` are what "`S` is the spectrum of a henselian local ring, pointed at its closed point"
amounts to without naming a ring; the first holds for `S = Spec A` at the closed point by
`AlgebraicGeometry.Spec_stalkClosedPointIso`.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
* [Stacks Project, Tag 05KS](https://stacks.math.columbia.edu/tag/05KS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **A section of a formally unramified morphism locally of finite type is an open immersion.**
The section `s` is the base change of the diagonal of `e` along `s` itself, and the diagonal of a
formally unramified morphism locally of finite type is an open immersion. -/
@[sga "3 VIB 2.7.1" "necessity, special case"]
theorem isOpenImmersion_of_section_formallyUnramified
    {X Y : Scheme.{u}} (e : X ⟶ Y) (s : Y ⟶ X) (hse : s ≫ e = 𝟙 Y)
    [FormallyUnramified e] [LocallyOfFiniteType e] : IsOpenImmersion s := by
  let k : X ⟶ pullback e e := pullback.lift (𝟙 X) (e ≫ s) (by simp [Category.assoc, hse])
  have hpb : IsPullback s s (pullback.diagonal e) k := by
    apply IsPullback.mk'
    · apply pullback.hom_ext
      · simp only [k, Category.assoc, pullback.diagonal_fst, pullback.lift_fst, Category.comp_id]
      · simp only [k, Category.assoc, pullback.diagonal_snd, pullback.lift_snd]
        simp [reassoc_of% hse]
    · intro T x y hxs _
      simpa [hse] using hxs =≫ e
    · intro T x y hxy
      have hfst : x = y := by
        simpa only [k, Category.assoc, pullback.diagonal_fst, pullback.lift_fst,
          Category.comp_id, Category.id_comp] using hxy =≫ pullback.fst e e
      have hsnd : x = y ≫ e ≫ s := by
        simpa only [k, Category.assoc, pullback.diagonal_snd, pullback.lift_snd,
          Category.comp_id, Category.id_comp] using hxy =≫ pullback.snd e e
      exact ⟨y ≫ e, hsnd.symm, hsnd.symm.trans hfst⟩
  exact MorphismProperty.of_isPullback hpb inferInstance

/-- **An elementary étale neighbourhood of a henselian local scheme collapses.** Let `f : X ⟶ S`
be étale and let `x ∈ X`. If the local ring of `S` at `f x` is henselian, if `S` is the local
scheme of that point (`IsIso (S.fromSpecStalk (f x))`), and if `f` induces an isomorphism on the
residue fields at `x` — that is, `(X, x)` is an *elementary* étale neighbourhood of `(S, f x)` —
then `Spec 𝒪_{X, x} ⟶ S` is an isomorphism.

This is the step of the proof of Stacks 05U7 which disposes of the elementary étale neighbourhood
supplied by Stacks 05MF: over a henselian base the base change to the local scheme of the
neighbourhood is the identity, so the free sections 05MF produces are already sections on the
given scheme. -/
@[ega "IV 18.5.11" "a ⇒ b"]
theorem isIso_fromSpecStalk_comp_of_henselian
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X)
    [HenselianLocalRing (S.presheaf.stalk (f x))]
    [IsIso (S.fromSpecStalk (f x))] [IsIso (f.residueFieldMap x)] :
    IsIso (X.fromSpecStalk x ≫ f) := by
  classical
  let R := S.presheaf.stalk (f x)
  have : IsHenselization R (ResidueField R) R :=
    IsHenselization.of_ind_etale.{u, u, 0} inferInstance
      (ObjectProperty.le_ind (CommAlgCat.etale R) (CommAlgCat.of R R)
        (inferInstanceAs (Algebra.Etale R R))) ⟨RingEquiv.refl _, fun _ => rfl⟩
  let U : ElementaryEtaleNeighborhood S (f x) :=
    ⟨{ scheme := X, point := x, toBase := f, map_point := rfl }, by
      simpa [EtaleNeighborhood.IsElementary, EtaleNeighborhood.residueFieldMap] using
        (inferInstanceAs (IsIso (f.residueFieldMap x)))⟩
  obtain ⟨ι, _, hover, _⟩ := isColimit_globalSections S (f x) R
  obtain ⟨g, hg, hgf, _⟩ := hover (.op U)
  let ρ : X.presheaf.stalk x ⟶ R := CommRingCat.ofHom g
  have : IsLocalHom g := hg
  have hring : g.comp (f.stalkMap x).hom = RingHom.id (S.presheaf.stalk (f x) : Type u) := by
    simpa [stalkMap, U, R] using hgf
  have hcomp : f.stalkMap x ≫ ρ = 𝟙 R := CommRingCat.hom_ext hring
  let β : Spec R ⟶ X := Spec.map ρ ≫ X.fromSpecStalk x
  have hfac : β ≫ f = S.fromSpecStalk (f x) := by
    dsimp only [β]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, hcomp, Spec.map_id, Category.id_comp]
  let σ : S ⟶ X := inv (S.fromSpecStalk (f x)) ≫ β
  have : IsOpenImmersion σ :=
    isOpenImmersion_of_section_formallyUnramified f σ (by simp [σ, hfac])
  have : IsOpenImmersion β := by
    rw [show β = S.fromSpecStalk (f x) ≫ σ by simp [σ]]
    infer_instance
  -- The closed point of `Spec R`, named at the type of a *point of the scheme*. Elaborated in
  -- place, `closedPoint R` has type `PrimeSpectrum R`, and the identification of that with
  -- `↥(Spec R)` is not available at the transparency at which `rw` checks type-correctness.
  let z : ↥(Spec R) := closedPoint R
  have hβx : β z = x := by
    show X.fromSpecStalk x (PrimeSpectrum.comap g (closedPoint R)) = x
    rw [IsLocalRing.comap_closedPoint g, Scheme.fromSpecStalk_closedPoint]
  have : IsIso (β.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 z
  have hz : IsIso ((β ≫ f).stalkMap z) := by
    rw [hfac]
    infer_instance
  have hi : IsIso (f.stalkMap (β z) ≫ β.stalkMap z) := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact hz
  have : IsIso (f.stalkMap (β z)) := (isIso_comp_right_iff _ _).mp hi
  have : IsIso (f.stalkMap x) := by rwa [hβx] at this
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
  infer_instance

/-- **The collapse, for an elementary étale neighbourhood.** If the local ring of `S` at `s` is
henselian and `S` is the local scheme of `s`, then for every elementary étale neighbourhood `N`
of `(S, s)` the morphism `Spec 𝒪_{N, n} ⟶ S` along which Stacks 05MF base changes is an
isomorphism.

This is the form in which the hypothesis arises from
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finiteType`, whose
conclusion is phrased in terms of `N.scheme.fromSpecStalk N.point ≫ N.toBase`. -/
@[sga "3 XI 1.11" "special case"]
theorem EtaleNeighborhood.isIso_fromSpecStalk_comp_toBase_of_henselian
    {S : Scheme.{u}} {s : S} (N : EtaleNeighborhood S s) (hN : N.IsElementary)
    [HenselianLocalRing (S.presheaf.stalk s)] [IsIso (S.fromSpecStalk s)] :
    IsIso (N.scheme.fromSpecStalk N.point ≫ N.toBase) := by
  have hpt : N.toBase N.point = s := N.map_point
  have : HenselianLocalRing (S.presheaf.stalk (N.toBase N.point)) := by
    rw [hpt]
    infer_instance
  have : IsIso (S.fromSpecStalk (N.toBase N.point)) := by
    rw [hpt]
    infer_instance
  have : IsIso (N.toBase.residueFieldMap N.point) := N.isElementary_iff.mp hN
  exact isIso_fromSpecStalk_comp_of_henselian N.toBase N.point

end AlgebraicGeometry

end
