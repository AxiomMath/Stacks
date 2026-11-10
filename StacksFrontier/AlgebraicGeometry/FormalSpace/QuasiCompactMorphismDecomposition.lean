module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionTfae
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationOnSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteFormalAtlas
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Decomposing a fibre product over a quasi-compact test object (Stacks 0AJB, (3) ⇒ (2))

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S`. **Stacks 0AJB** lists four equivalent conditions on `f`,
of which condition (3) — the definition of a quasi-compact morphism, Stacks 0AJC — asks that
every fibre product `X ×_Y T` with an *affine* scheme `T` over `S` in the site mapping to `Y` be
a quasi-compact formal algebraic space over `S`, and condition (2) asks the same over every
*quasi-compact* scheme in the site.

This file proves the implication **(3) ⇒ (2)**: a quasi-compact scheme over `S` in the site is
covered by finitely many affine opens, which are again objects of the site, so `X ×_Y T` is
covered by the finitely many quasi-compact formal algebraic spaces `X ×_Y U_i`, and a sheaf
covered by finitely many quasi-compact formal algebraic spaces along representable étale
morphisms is itself one. Together with the converse, which is
`AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges.isQuasiCompact`, this closes
the first cycle among the four conditions of Stacks 0AJB: conditions (2) and (3) are equivalent
with no hypothesis.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_yonedaSheafMap`: the representable sheaf
  of an étale morphism of the big fppf site of `S` is representable by algebraic spaces and
  étale.
* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_finite_isRepresentableEtale_cover`: a
  sheaf covered by finitely many quasi-compact formal algebraic spaces over `S` along
  representable étale morphisms is a quasi-compact formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges`:
  **Stacks 0AJB**, the implication (3) ⇒ (2).
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompactOnSchemeBaseChanges`:
  **Stacks 0AJB**, the equivalence of conditions (2) and (3).

## Implementation notes

Three ingredients go into the decomposition, and the first two are the reusable ones.

The finite affine covering of the test object is
`AlgebraicGeometry.BigFppfOver.exists_finite_affine_open_cover`, a finite subcover of the affine
open cover of the underlying scheme read inside the site; its members are objects of the site by
Stacks 000R (3), and finiteness is what makes the reassembly possible.

The assembly step is
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_finite_isRepresentableEtale_cover`. It
strengthens the implication (2) ⇒ (3) of Stacks 0AJ9,
`AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas.isQuasiCompactSpace`, in two ways: the
members of the finite covering family need only be *quasi-compact* formal algebraic spaces
rather than affine ones, each contributing the single affine formal algebraic space its
quasi-compactness provides, and the set-theoretic condition of Stacks 0AIS on the target is a
conclusion rather than a hypothesis. The latter is because a finite — hence countable — family
as in Definition 0AIM already forces that condition, by observation (3) of Stacks 0AIS,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`; so the
assembly asks for nothing beyond the covering family itself, which is what makes the
implication of Stacks 0AJB unconditional. Stacks 0AJ9 enters only through its implication
(2) ⇒ (3), and that implication is itself unconditional, both of the assertions about
coproducts it rests on being available:
`AlgebraicGeometry.FormalSpace.finiteCoproductsAffineFormal` and
`AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale'`.

Joint surjectivity of the family `{X ×_Y U_i ⟶ X ×_Y T}` is the one step that is not formal.
The family `{U_i ⟶ T}` generates a covering sieve, so the induced map from the coproduct of the
representable sheaves onto the representable sheaf of `T` is a surjection of sheaves
(`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_yonedaSheaf`); its base change
along `X ×_Y T ⟶ T` is therefore a surjection of sheaves as well, and that base change is the
coproduct of the base changes of the summands because coproducts of sheaves of types are
universal — `CategoryTheory.Sheaf.exists_isColimit_cofan_pullback_of_comp`. The members of the
covering family are written as `Sigma.ι ≫ Sigma.desc` rather than as the maps they are equal to,
so that the fibre products the decomposition produces are the ones the family is indexed by on
the nose; `Sigma.ι_comp_desc` relates them where a property of a member is needed.

Representable étaleness of the covering family comes from
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_yonedaSheafMap`, an open immersion of
schemes being étale. Both halves of that statement are read off relative étaleness of the
universe-lifted Yoneda image of the morphism of the site,
`AlgebraicGeometry.Space.relative_etale_uliftYoneda_map_iff`: representability because a
relative property along the universe-lifted Yoneda embedding carries a representing object of
the site for every represented base change, and étaleness because relative étaleness is stable
under base change and under composition, the latter being exactly what
`AlgebraicGeometry.Space.IsEtaleULift` asks for.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The representable sheaf of an étale morphism of the site -/

/-- **The representable sheaf of an étale morphism of the big fppf site of `S` is representable
by algebraic spaces and étale.** These are therefore maps of the kind the coverings of
Definition 0AIM are made of, and in particular an affine open covering of an object of the site
is one.

The universe-lifted Yoneda image of an étale morphism of the site is étale after every
represented base change, by `AlgebraicGeometry.Space.relative_etale_uliftYoneda_map_iff`, and
both clauses follow from that. Representability does because such a relative property supplies,
for every scheme-valued point of the target, an object of the site representing the base change,
and the universe-lifted Yoneda presheaf of an object of the site is an algebraic space over `S`.
Étaleness does because the relative property is stable under base change, so it holds for the
projection of each base change, and `AlgebraicGeometry.Space.IsEtaleULift` of a morphism is
implied by the relative property of that morphism, the relative property being stable under
composition. -/
theorem isRepresentableEtale_yonedaSheafMap {V T : BigFppfOver B S hS} (v : V ⟶ T)
    (hv : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map v)) :
    IsRepresentableEtale B S hS
      (⟨(uliftYoneda.{u + 1}).map v⟩ : yonedaSheaf B S hS V ⟶ yonedaSheaf B S hS T) :=
  isRepresentableEtale_of_relative_etaleOnSite B S hS _
    ((Space.relative_etale_uliftYoneda_map_iff.{u + 1} B S hS v).mpr hv)

/-! ### Assembling finitely many quasi-compact pieces -/

/-- A morphism of fppf sheaves that is a composite of two epimorphisms is locally surjective. -/
private theorem isLocallySurjective_of_eq_comp_of_epi {X Y Z : FppfSheaf B S hS} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : X ⟶ Z} [Epi f] [Epi g] (hh : h = f ≫ g) : Sheaf.IsLocallySurjective h :=
  (Sheaf.isLocallySurjective_iff_epi _).mpr (hh ▸ inferInstance)

/-- **A sheaf covered by finitely many quasi-compact formal algebraic spaces over `S` along
representable étale morphisms is a quasi-compact formal algebraic space over `S`.**

Each member of the covering family carries, by its quasi-compactness, a single affine formal
algebraic space mapping onto it by a representable étale surjection of sheaves; composing with
the member gives a family as in Definition 0AIM, indexed by the same finite type, and the
implication (2) ⇒ (3) of Stacks 0AJ9,
`AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas.isQuasiCompactSpace`, assembles it into a
single affine formal algebraic space surjecting onto the target. Surjectivity of the composite
family is epimorphy of the coproduct of the chosen charts followed by the given surjection.

The set-theoretic condition of Stacks 0AIS on the target is not a hypothesis: the assembled
family is finite, hence countable, so observation (3) of Stacks 0AIS,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_atlas`, supplies
it. -/
theorem isQuasiCompactSpace_of_finite_isRepresentableEtale_cover {X : FppfSheaf B S hS}
    {I : Type (u + 1)} [Finite I] (Xi : I → FppfSheaf B S hS) (c : ∀ i, Xi i ⟶ X)
    (hc : ∀ i, IsRepresentableEtale B S hS (c i))
    (hXi : ∀ i, IsQuasiCompactSpace B S hS (Xi i))
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c)) :
    IsQuasiCompactSpace B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  choose Z z hZaff hzet hzsurj using fun i => (hXi i).2
  have hzepi : ∀ i, Epi (z i) := fun i => (Sheaf.isLocallySurjective_iff_epi _).mp (hzsurj i)
  have hcepi : Epi (Sigma.desc c) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
  have hfac : (Sigma.desc fun i => z i ≫ c i) = Limits.Sigma.map z ≫ Sigma.desc c :=
    Sigma.hom_ext _ _ fun i => by simp
  have hdsurj : Sheaf.IsLocallySurjective (Sigma.desc fun i => z i ≫ c i) :=
    isLocallySurjective_of_eq_comp_of_epi B S hS hfac
  have hdet : ∀ i, IsRepresentableEtale B S hS (z i ≫ c i) := fun i =>
    IsRepresentableEtale.comp B S hS (hzet i) (hc i)
  exact HasFiniteFormalAtlas.isQuasiCompactSpace' B S hS
    ⟨satisfiesSetTheoreticCondition_of_countable_atlas B S hS X Z (fun i => z i ≫ c i)
        ⟨hZaff, hdet, hdsurj⟩,
      I, Z, fun i => z i ≫ c i, inferInstance, hZaff, hdet, hdsurj⟩

/-! ### The implication (3) implies (2) -/

/-- **Stacks 0AJB, condition (3) implies condition (2).** Let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S` every one of whose fibre products with an affine scheme over
`S` in the site mapping to `Y` is a quasi-compact formal algebraic space over `S`. Then the same
holds over every *quasi-compact* scheme over `S` in the site.

Let `T` be such a scheme and let `W` be a fibre product of `f` with a point `T ⟶ Y`. A finite
affine open covering `{U_i ⟶ T}` of `T` inside the site exists because `T` is quasi-compact
(`AlgebraicGeometry.BigFppfOver.exists_finite_affine_open_cover`). Each `W ×_T U_i` is, by
pasting the two cartesian squares, a fibre product of `f` with the affine point `U_i ⟶ Y`, hence
a quasi-compact formal algebraic space by the hypothesis; each projection `W ×_T U_i ⟶ W` is a
base change of `U_i ⟶ T`, hence representable étale, an open immersion being étale; and the
family of projections is jointly surjective because `{U_i ⟶ T}` generates a covering sieve and
coproducts of sheaves of types are stable under base change. So
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_finite_isRepresentableEtale_cover`
applies. -/
@[stacks 0AJB "condition (3) implies condition (2)"]
theorem IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsQuasiCompact B S hS f) : IsQuasiCompactOnSchemeBaseChanges B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro T hT g W p q sq
  obtain ⟨I, V, v, hIfin, hVaff, hVopen, hcov⟩ :=
    BigFppfOver.exists_finite_affine_open_cover B S hS T
  set F : ULift.{u + 1} I → FppfSheaf B S hS := fun i => yonedaSheaf B S hS (V i.down)
  set γ : ∀ i, F i ⟶ yonedaSheaf B S hS T :=
    fun i => ⟨(uliftYoneda.{u + 1}).map (v i.down)⟩
  have hγet : ∀ i, IsRepresentableEtale B S hS (γ i) := fun i =>
    isRepresentableEtale_yonedaSheafMap B S hS (v i.down)
      (by have := hVopen i.down; infer_instance)
  have hγsurj : Sheaf.IsLocallySurjective (Sigma.desc γ) := by
    rw [Sheaf.isLocallySurjective_sigmaDesc_iff]
    intro W s
    refine ⟨Sieve.pullback s.down (Sieve.ofArrows V v),
      (BigFppfOver.topology B S hS).pullback_stable _ hcov, ?_⟩
    rintro Z g ⟨Wi, b, c, ⟨i⟩, hfac⟩
    exact ⟨ULift.up i, ULift.up b, congrArg ULift.up hfac⟩
  obtain ⟨l, hl₁, hl₂, ⟨hlcol⟩⟩ := Sheaf.exists_isColimit_cofan_pullback_of_comp
    (BigFppfOver.topology B S hS) (Sigma.ι F) (coproductIsCoproduct F) (Sigma.desc γ) p
  refine isQuasiCompactSpace_of_finite_isRepresentableEtale_cover B S hS
    (fun i => pullback p (Sigma.ι F i ≫ Sigma.desc γ))
    (fun i => pullback.fst p (Sigma.ι F i ≫ Sigma.desc γ)) (fun i => ?_) (fun i => ?_) ?_
  · exact isRepresentableEtale_of_isPullback B S hS
      (IsPullback.of_hasPullback p (Sigma.ι F i ≫ Sigma.desc γ)).flip
      (by rw [Sigma.ι_comp_desc]; exact hγet i)
  · exact h (V i.down) (hVaff i.down) ((Sigma.ι F i ≫ Sigma.desc γ) ≫ g) _
      (pullback.snd p (Sigma.ι F i ≫ Sigma.desc γ))
      (pullback.fst p (Sigma.ι F i ≫ Sigma.desc γ) ≫ q)
      ((IsPullback.of_hasPullback p (Sigma.ι F i ≫ Sigma.desc γ)).flip.paste_vert sq)
  · have hfstsurj : Sheaf.IsLocallySurjective (pullback.fst p (Sigma.desc γ)) := by
      have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
          ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
            (Sigma.desc γ)) := hγsurj
      exact Presheaf.isLocallySurjective_of_isPullback (J := BigFppfOver.topology B S hS)
        ((IsPullback.of_hasPullback p (Sigma.desc γ)).map
          (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))
    have : Epi (pullback.fst p (Sigma.desc γ)) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp hfstsurj
    set e := (coproductIsCoproduct
      (fun i => pullback p (Sigma.ι F i ≫ Sigma.desc γ))).coconePointUniqueUpToIso hlcol
      with hedef
    have he : e.hom ≫ pullback.fst p (Sigma.desc γ) =
        Sigma.desc fun i => pullback.fst p (Sigma.ι F i ≫ Sigma.desc γ) := by
      refine Sigma.hom_ext _ _ fun i => ?_
      have hcomp := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct fun i => pullback p (Sigma.ι F i ≫ Sigma.desc γ)) hlcol
        (Discrete.mk i)
      simp only [Cofan.mk_ι_app] at hcomp
      rw [← Category.assoc, hedef, hcomp, hl₁ i]
      exact (Sigma.ι_comp_desc (fun i => pullback.fst p (Sigma.ι F i ≫ Sigma.desc γ)) i).symm
    exact isLocallySurjective_of_eq_comp_of_epi B S hS he.symm

/-- **Stacks 0AJB, the equivalence of conditions (2) and (3).** For a morphism of fppf sheaves
on the big fppf site of `S`, the fibre product condition over the quasi-compact schemes over `S`
in the site and the fibre product condition over the affine ones are equivalent.

One implication restricts the quantifier, an affine scheme being quasi-compact, and is
`AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges.isQuasiCompact`; the other is
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges`. This is the
first cycle closed among the four conditions of Stacks 0AJB. -/
@[stacks 0AJB "the equivalence of conditions (2) and (3)"]
theorem isQuasiCompact_iff_isQuasiCompactOnSchemeBaseChanges {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) :
    IsQuasiCompact B S hS f ↔ IsQuasiCompactOnSchemeBaseChanges B S hS f :=
  ⟨IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges B S hS,
    IsQuasiCompactOnSchemeBaseChanges.isQuasiCompact B S hS⟩

end AlgebraicGeometry.FormalSpace

end
