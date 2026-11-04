module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Hom.HomFunctorMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModuleHomSheaf

/-!
# Étale descent of homomorphisms for the relative Hom functor

In the relative Hom situation of [Stacks, Tag 08JT] — a morphism `f : X ⟶ base` of algebraic spaces
and two `𝒪_X`-modules `F`, `G` — let `g : U ⟶ T` be a surjective étale morphism of algebraic spaces
over the base, with kernel pair `p, q : R ⟶ U`. A homomorphism `w : F_U ⟶ G_U` of the modules
pulled back to `X_U = X ×_{base} U` whose two pullbacks to `X_R` agree is the pullback of a
homomorphism `F_T ⟶ G_T`; this is the fullness clause of [Stacks, Tag 04W8] for the one-member
étale covering `X_U ⟶ X_T` of base changes. Consequently the morphisms `T ⟶ Hom(F, G)` are the
pairs `(h, u)` with `h : T ⟶ base` and `u : F_T ⟶ G_T` [Stacks, Tag 0D3S].

## Main results

* `AlgebraicGeometry.Space.exists_lift_overBaseChange_of_isPullback`: two morphisms into `X_U`
  with equal images in `X_T` factor through `X_R`, the base change of a kernel pair of `g`.
* `AlgebraicGeometry.Space.HomSituation.exists_conjHom_spaceBaseChangeComparison_eq`: **descent of
  homomorphisms of arbitrary `𝒪`-modules on `X` along `X_U ⟶ X_T`**, given the agreement of the
  two pullbacks along a kernel pair of `g`.
* `AlgebraicGeometry.Space.HomSituation.etaleHomDescent`: consequently the fullness clause
  `AlgebraicGeometry.Space.HomSituation.EtaleHomDescent` holds for every Hom situation.
* `AlgebraicGeometry.Space.HomSituation.bijective_morOfSpaceHom` and
  `AlgebraicGeometry.Space.HomSituation.spaceHomPairEquiv`: the bijection between the pairs
  `(h, u)` at an algebraic space `T` and the morphisms `T ⟶ Hom(F, G)`.

## Implementation notes

`Hom(F, G)` is `AlgebraicGeometry.Space.HomSituation.homSitePresheaf` at the pseudofunctoriality
`AlgebraicGeometry.Space.modulePushforwardCoherence` of the direct images ([Stacks, Tag 03LU]).
The morphisms of sheaves out of `T` are morphisms of presheaves out of the universe lift of `T`.

## References

* [Stacks Project, Tag 0D3S](https://stacks.math.columbia.edu/tag/0D3S)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Two morphisms into a base change with equal images in a further base change factor
through the base change of a kernel pair.**  If `p, q : R ⟶ U` is a kernel pair of
`g : U ⟶ T` over `Y`, two morphisms `a, b : K ⟶ X_U` with `a ≫ X_g = b ≫ X_g` are
`c ≫ X_p` and `c ≫ X_q` for a morphism `c : K ⟶ X_R`. -/
theorem exists_lift_overBaseChange_of_isPullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U T R : Over Y} (g : U ⟶ T) (p q : R ⟶ U)
    (hpb : IsPullback p.left.hom q.left.hom g.left.hom g.left.hom)
    {K : AlgebraicSpaces B S hS} (a b : K ⟶ overBaseChange f U)
    (hab : a ≫ overBaseChangeMap f g = b ≫ overBaseChangeMap f g) :
    ∃ c : K ⟶ overBaseChange f R,
      c ≫ overBaseChangeMap f p = a ∧ c ≫ overBaseChangeMap f q = b := by
  have hab' : (a ≫ overInclusion f U).hom ≫ g.left.hom =
      (b ≫ overInclusion f U).hom ≫ g.left.hom := by
    have h := congrArg (· ≫ overInclusion f T) hab
    simp only [Category.assoc, overBaseChangeMap_comp_inclusion] at h
    exact congrArg (fun z => z.hom) h
  let r : K ⟶ R.left := ObjectProperty.homMk (hpb.lift _ _ hab')
  have hr1 : r ≫ p.left = a ≫ overInclusion f U :=
    ObjectProperty.hom_ext _ (hpb.lift_fst _ _ hab')
  have hr2 : r ≫ q.left = b ≫ overInclusion f U :=
    ObjectProperty.hom_ext _ (hpb.lift_snd _ _ hab')
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS f R.hom
  have hU : overProjection f U ≫ f = overInclusion f U ≫ U.hom :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.hom).w
  have hcomm : (a ≫ overProjection f U) ≫ f = r ≫ R.hom := by
    rw [← Over.w p, ← Category.assoc, hr1, Category.assoc, Category.assoc, hU]
  let c : K ⟶ overBaseChange f R := hP.lift _ _ hcomm
  have hc1 : c ≫ overProjection f R = a ≫ overProjection f U := hP.lift_fst _ _ hcomm
  have hc2 : c ≫ overInclusion f R = r := hP.lift_snd _ _ hcomm
  refine ⟨c, overBaseChange_hom_ext f ?_ ?_, overBaseChange_hom_ext f ?_ ?_⟩
  · rw [Category.assoc, overBaseChangeMap_comp_projection, hc1]
  · rw [Category.assoc, overBaseChangeMap_comp_inclusion, ← Category.assoc, hc2, hr1]
  · rw [Category.assoc, overBaseChangeMap_comp_projection, hc1,
      ← overBaseChangeMap_comp_projection f g, ← Category.assoc, hab, Category.assoc]
  · rw [Category.assoc, overBaseChangeMap_comp_inclusion, ← Category.assoc, hc2, hr2]

namespace HomSituation

variable (s : HomSituation B S hS)

/-- Pullback of a homomorphism along a morphism of algebraic spaces over the base is its
restricted reading along the morphism of base changes. -/
theorem conjHom_spaceBaseChangeComparison_eq_restrictForm {U T : Over s.base} (g : U ⟶ T)
    {M N : Modules.{u, u} B S hS s.X.1 s.X.2}
    (α : (modulePullback B S hS (overProjection s.f T)).obj M ⟶
      (modulePullback B S hS (overProjection s.f T)).obj N) :
    Functor.conjHom (s.spaceBaseChangeComparison g) α =
      QuasiCoherentDescent.restrictForm B S hS (overBaseChangeMap s.f g) (overProjection s.f T)
        (overProjection s.f U) (overBaseChangeMap_comp_projection s.f g) α :=
  conjHom_modulePullbackTriangle_eq_restrictForm B S hS _ α

/-- **Descent of homomorphisms along a surjective étale morphism of algebraic spaces over the
base.**  For `g : U ⟶ T` surjective étale with kernel pair `p, q : R ⟶ U`, a homomorphism
`w : M_U ⟶ N_U` of two `𝒪_X`-modules pulled back to `X_U` whose pullbacks along `p` and `q`
agree is the pullback along `g` of a homomorphism `M_T ⟶ N_T`. -/
theorem exists_conjHom_spaceBaseChangeComparison_eq {M N : Modules.{u, u} B S hS s.X.1 s.X.2}
    {U T : Over s.base} (g : U ⟶ T) (hsurj : IsSurjective B S hS g.left.hom)
    (hetale : IsEtale B S hS g.left.hom) {R : Over s.base} (p q : R ⟶ U)
    (hpb : IsPullback p.left.hom q.left.hom g.left.hom g.left.hom)
    (w : (modulePullback B S hS (overProjection s.f U)).obj M ⟶
      (modulePullback B S hS (overProjection s.f U)).obj N)
    (hw : Functor.conjHom (s.spaceBaseChangeComparison p) w =
      Functor.conjHom (s.spaceBaseChangeComparison q) w) :
    ∃ α : (modulePullback B S hS (overProjection s.f T)).obj M ⟶
        (modulePullback B S hS (overProjection s.f T)).obj N,
      Functor.conjHom (s.spaceBaseChangeComparison g) α = w := by
  have hcov := s.isEtaleCovering_overBaseChangeMap g hsurj hetale
  rw [s.conjHom_spaceBaseChangeComparison_eq_restrictForm p,
    s.conjHom_spaceBaseChangeComparison_eq_restrictForm q] at hw
  obtain ⟨t, ht, -⟩ := existsUnique_restrictForm_eq B S hS (M := M) (N := N)
    (overProjection s.f T) (fun _ : PUnit.{u + 1} => overBaseChange s.f U)
    (fun _ => overBaseChangeMap s.f g) (fun _ => hcov.etale PUnit.unit) hcov
    (fun _ => overProjection s.f U) (fun _ => overBaseChangeMap_comp_projection s.f g)
    (fun _ => w) (fun i j h => by
      obtain ⟨c, hc1, hc2⟩ := exists_lift_overBaseChange_of_isPullback s.f g p q hpb
        (QuasiCoherentDescent.pairFst B S hS (fun _ : PUnit.{u + 1} => overBaseChange s.f U)
          (fun _ => overBaseChangeMap s.f g) i j)
        (QuasiCoherentDescent.pairSnd B S hS (fun _ : PUnit.{u + 1} => overBaseChange s.f U)
          (fun _ => overBaseChangeMap s.f g) i j)
        (QuasiCoherentDescent.pair_condition B S hS _ _ i j)
      have hct : c ≫ overProjection s.f R =
          QuasiCoherentDescent.pairFst B S hS (fun _ : PUnit.{u + 1} => overBaseChange s.f U)
            (fun _ => overBaseChangeMap s.f g) i j ≫ overProjection s.f U := by
        rw [← overBaseChangeMap_comp_projection s.f p, ← Category.assoc, hc1]
      have e1 := QuasiCoherentDescent.restrictForm_comp B S hS c (overBaseChangeMap s.f p)
        (overProjection s.f U) (overProjection s.f R) (overBaseChangeMap_comp_projection s.f p)
        _ hc1 _ hct rfl w
      have e2 := QuasiCoherentDescent.restrictForm_comp B S hS c (overBaseChangeMap s.f q)
        (overProjection s.f U) (overProjection s.f R) (overBaseChangeMap_comp_projection s.f q)
        _ hc2 _ hct h w
      exact e1.symm.trans ((congrArg (QuasiCoherentDescent.restrictForm B S hS c
        (overProjection s.f R) _ hct) hw).trans e2))
  exact ⟨t, (s.conjHom_spaceBaseChangeComparison_eq_restrictForm g t).trans (ht PUnit.unit)⟩

/-- Every Hom situation satisfies `AlgebraicGeometry.Space.HomSituation.EtaleHomDescent`:
homomorphisms `F_U ⟶ G_U` whose two pullbacks along a kernel pair of a surjective étale `g : U ⟶ T`
agree are pullbacks of homomorphisms `F_T ⟶ G_T`. -/
theorem etaleHomDescent : s.EtaleHomDescent where
  exists_homOverSpaceMap_eq g hsurj hetale _ p q hpb w hw :=
    s.exists_conjHom_spaceBaseChangeComparison_eq (M := s.F) (N := s.G) g hsurj hetale p q hpb w hw

/-! ### The identification `Mor(T, Hom(F, G)) = {(h, u)}` -/

/-- For an algebraic space `T` over `S`, the morphisms of sheaves `T ⟶ Hom(F, G)` are the pairs
`(h, u)` of a morphism `h : T ⟶ base` and a homomorphism `u : F_T ⟶ G_T` of the two modules pulled
back to `X ×_{base, h} T`: the construction `(h, u) ↦ (a ↦ (h ∘ a, a^*u))`, which is
`AlgebraicGeometry.Space.HomSituation.morOfSpaceHom`, is a bijection. -/
@[stacks 0D3S "Mor(T, Hom(F, G)) = {(h, u)}: the construction (h, u) ↦ (a ↦ (h ∘ a, a^*u)) \
is a bijection from the pairs onto the morphisms T ⟶ Hom(F, G), for every algebraic space T"]
theorem bijective_morOfSpaceHom (T : AlgebraicSpaces B S hS) :
    Function.Bijective (s.morOfSpaceHom (modulePushforwardCoherence B S hS) (T := T)) := by
  refine ⟨fun p p' e => ?_, fun v => ?_⟩
  · have hb : p.toBase = p'.toBase := by
      rw [← s.baseOfMor_morOfSpaceHom (modulePushforwardCoherence B S hS) p, e,
        s.baseOfMor_morOfSpaceHom]
    obtain ⟨b, u⟩ := p
    obtain ⟨b', u'⟩ := p'
    obtain rfl : b = b' := hb
    obtain rfl : u = u' :=
      s.injective_morOver (modulePushforwardCoherence B S hS) b (Subtype.ext e)
    rfl
  · obtain ⟨u, hu⟩ := s.surjective_morOver (modulePushforwardCoherence B S hS) s.etaleHomDescent
      (s.baseOfMor (modulePushforwardCoherence B S hS) v) ⟨v, rfl⟩
    exact ⟨⟨_, u⟩, congrArg Subtype.val hu⟩

/-- **The identification `Mor(T, Hom(F, G)) = {(h, u)}`, as an equivalence.** Its forward
direction is `AlgebraicGeometry.Space.HomSituation.morOfSpaceHom`. -/
def spaceHomPairEquiv (T : AlgebraicSpaces B S hS) :
    s.SpaceHomPair T ≃
      (T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf (modulePushforwardCoherence B S hS)) :=
  Equiv.ofBijective _ (s.bijective_morOfSpaceHom T)

/-- **The relative Hom functor of Stacks 08JT on the test schemes over the base is the
restriction of the one indexed by the algebraic spaces over the base.**  The functor
`Hom(F, G) : (Sch/base)^{opp} ⥤ Sets` of Stacks 08JT is
`AlgebraicGeometry.Space.HomSituation.homOverSpaceFunctor` composed with the inclusion
`AlgebraicGeometry.Space.schemesOverToOver` of the test schemes over the base into the
algebraic spaces over the base.

The two sides are the same functor on the nose: base change along a test scheme is base change
along the algebraic space it names, and the coherence datum the left-hand side carries is used
only in the two functor laws, which are propositions. -/
@[stacks 08JT "the Hom functor on the test schemes over the base is the restriction of the \
Hom functor indexed by the algebraic spaces over the base"]
theorem homFunctor_eq_restriction (hc : ModulePushforwardCoherence B S hS) :
    s.homFunctor hc = (schemesOverToOver s.base).op ⋙ s.homOverSpaceFunctor :=
  rfl

end HomSituation

end AlgebraicGeometry.Space

end
