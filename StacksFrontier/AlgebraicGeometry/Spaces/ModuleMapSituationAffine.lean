module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional

/-!
# The base-change loci of a map of quasi-coherent modules under an affine morphism

In Situation Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces and a map `u : F ⟶ G`
of quasi-coherent `𝒪_X`-modules, with the four loci `F_{iso}`, `F_{inj}`, `F_{surj}`,
`F_{zero}` on the schemes over `Y` — two lemmas compare the loci of `u` with the loci of a
companion map produced by an affine morphism.

* Stacks 0CW8: an affine `g : X ⟶ X'` over `Y` replaces `u` by `u' = g_*u`, and all four loci
  are unchanged.
* Stacks 0CW7: an affine `i : Z ⟶ X` with `G = i_*H` replaces `u` by its adjoint
  `v : i^*F ⟶ H`, and the vanishing loci agree; for a closed immersion the surjectivity loci
  agree too.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.affinePushforward` — the situation of `u' = g_*u`
  of Stacks 0CW8.
* `AlgebraicGeometry.Space.ModuleMapSituation.affinePushforwardBaseChange` — the morphism
  `g_T : X ×_Y T ⟶ X' ×_Y T` of base-change spaces induced by `g`.
* `AlgebraicGeometry.Space.ModuleMapSituation.PushforwardIdentifiesBaseChange` — the input the
  proof of Stacks 0CW8 takes from the affine base-change clause of Stacks 07U8 and from
  Stacks 08AI, at one test scheme.
* `AlgebraicGeometry.Space.AffineAdjointData` — the data of Stacks 0CW7, and its two
  situations `sourceSituation` (for `u`) and `adjointSituation` (for `v`).
* `AlgebraicGeometry.Space.AffineAdjointData.AdjointAfterBaseChange` — the input the proof of
  Stacks 0CW7 takes from the affine base-change clause of Stacks 07U8: that `u_T` and `v_T`
  are again adjoint.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor_affinePushforward_eq`,
  `injFunctor_affinePushforward_eq`, `surjFunctor_affinePushforward_eq`,
  `zeroFunctor_affinePushforward_eq` — Stacks 0CW8.
* `AlgebraicGeometry.Space.AffineAdjointData.zeroFunctor_adjointSituation_eq` — Stacks 0CW7,
  part (1).
* `AlgebraicGeometry.Space.AffineAdjointData.surjFunctor_adjointSituation_eq` — Stacks 0CW7,
  part (2).

## Implementation notes

### What is assumed, and why

The source's proof of Stacks 0CW8 is two sentences.  The first, "`g_{T,*}u_T = u'_T` by
Cohomology of Spaces, Lemma 07U8", is the affine base-change clause of Stacks 07U8; the
second, "`g_{T,*}` is a faithful, exact functor reflecting isomorphisms, injective maps and
surjective maps", is how the source uses Stacks 08AI.  Neither is available here: the module
carrying Stacks 07U8 in this repository,
`StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent`, proves only the
quasi-coherence clause, and the module carrying Stacks 08AI,
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectImageAffine`, carries only the
functor of its first sentence and records the equivalence as unproved and blocked on
Stacks 03M3.  So both enter as hypotheses, named for the results they are, in the pattern that
`AlgebraicGeometry.Space.AffinePushforwardEquivalence` and
`Stacks.Chow.ProperPushforwardDescends` already set in this repository.  Everything the source
leaves to the reader — that the four pointwise comparisons assemble into equalities of
subterminal functors, and that the pulled-back maps are the ones being compared — is proved.

The hypotheses are kept as weak as the proof allows.  The base-change clause enters only as an
isomorphism in the arrow category, which is what naturality of the comparison of Stacks 07U8
at `u` supplies and all that is used; the reflection clause enters only at the two modules
concerned, not as a statement about the functor.

### Why the affineness of `g_T` is not proved here

Affineness of the base change of an affine morphism is Stacks 03WI,
`AlgebraicGeometry.Space.IsAffineHom.of_isPullback`, and it is what justifies applying
Stacks 08AI to `g_T`.  Nothing below consumes it: the reflection properties of `g_{T,*}` are
hypotheses, so the affineness that would justify them is the reader's check on the hypothesis
and not a step of a proof here.

### The universe

Everything is at `Modules.{u, u}`, the module universe of the structure rings: that is the
universe at which `AlgebraicGeometry.Space.modulePullback`, its adjunction and
`AlgebraicGeometry.Space.modulePullbackSystem` are available, and hence the only universe at
which the four loci can be evaluated on the actual inverse image of modules.

## References

* [Stacks Project, Tag 0CW7](https://stacks.math.columbia.edu/tag/0CW7)
* [Stacks Project, Tag 0CW8](https://stacks.math.columbia.edu/tag/0CW8)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transfer of the four conditions along an isomorphism of arrows -/

section ArrowTransfer

variable {C : Type*} [Category C] {M N M' N' : C} {α : M ⟶ N} {β : M' ⟶ N'}

/-- An isomorphism of arrows writes the first arrow as a conjugate of the second. -/
private lemma eq_conj_of_arrowIso (e : Arrow.mk α ≅ Arrow.mk β) :
    α = e.hom.left ≫ β ≫ inv e.hom.right := by
  have hw : e.hom.left ≫ β = α ≫ e.hom.right := Arrow.w e.hom
  rw [← Category.assoc, hw, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Being an isomorphism transfers along an isomorphism of arrows. -/
private lemma isIso_iff_of_arrowIso (e : Arrow.mk α ≅ Arrow.mk β) : IsIso α ↔ IsIso β :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff e

/-- Being a monomorphism transfers along an isomorphism of arrows. -/
private lemma mono_iff_of_arrowIso (e : Arrow.mk α ≅ Arrow.mk β) : Mono α ↔ Mono β :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff e

/-- Being an epimorphism transfers along an isomorphism of arrows. -/
private lemma epi_iff_of_arrowIso (e : Arrow.mk α ≅ Arrow.mk β) : Epi α ↔ Epi β :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff e

/-- Vanishing transfers along an isomorphism of arrows. -/
private lemma eq_zero_iff_of_arrowIso [HasZeroMorphisms C] (e : Arrow.mk α ≅ Arrow.mk β) :
    α = 0 ↔ β = 0 := by
  rw [eq_conj_of_arrowIso e]
  constructor
  · intro h
    have h' : β ≫ inv e.hom.right = 0 := by
      rw [← cancel_epi e.hom.left, h, comp_zero]
    rw [← cancel_mono (inv e.hom.right), h', zero_comp]
  · intro h
    have h1 : e.hom.left ≫ β ≫ inv e.hom.right =
        e.hom.left ≫ (0 : M' ⟶ N') ≫ inv e.hom.right :=
      congrArg (fun t => e.hom.left ≫ t ≫ inv e.hom.right) h
    rw [h1, zero_comp, comp_zero]

end ArrowTransfer

/-! ### Two subterminal functors attached to equal conditions -/

namespace ModuleMapSituation

variable {B S hS}

/-- Two subterminal functors on the same category of test schemes attached to conditions that
agree pointwise are equal. -/
private lemma subterminalFunctor_congr_of_iff (D : ModuleMapSituation.{u, u} B S hS)
    {Q Q' : D.SchemesOver → Prop}
    (stable : ∀ {T T' : D.SchemesOver}, (T' ⟶ T) → Q T → Q T')
    (stable' : ∀ {T T' : D.SchemesOver}, (T' ⟶ T) → Q' T → Q' T')
    (h : ∀ T, Q T ↔ Q' T) :
    D.subterminalFunctor Q stable = D.subterminalFunctor Q' stable' := by
  have hQ : Q = Q' := funext fun T => propext (h T)
  subst hQ
  rfl

end ModuleMapSituation

/-! ### Stacks 0CW8: direct image along an affine morphism -/

namespace ModuleMapSituation

variable {B S hS} (D : ModuleMapSituation.{u, u} B S hS)
  {X' : AlgebraicSpaces B S hS} (g : D.X ⟶ X') (f' : X' ⟶ D.Y)

/-- The situation of Stacks 0CW8: the direct images `g_*F ⟶ g_*G` of the two modules and of
the map, over the same target algebraic space.

Quasi-coherence of the two direct images is the quasi-coherence clause of Stacks 07U8,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom`, whose own
hypothesis `h` is threaded through. -/
def affinePushforward (h07U8 : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hg : IsAffineHom B S hS g.hom) : ModuleMapSituation.{u, u} B S hS where
  X := X'
  Y := D.Y
  f := f'
  F := (modulePushforward B S hS g).obj D.F
  G := (modulePushforward B S hS g).obj D.G
  quasicoherent_F :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom B S hS h07U8 g hg D.F
      D.quasicoherent_F
  quasicoherent_G :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom B S hS h07U8 g hg D.G
      D.quasicoherent_G
  u := (modulePushforward B S hS g).map D.u

/-- The situation of Stacks 0CW8: the direct images `g_*F ⟶ g_*G` of the two modules and of
the map, over the same target algebraic space.

Quasi-coherence of the two direct images is the quasi-coherence clause of Stacks 07U8,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom`, which is
unconditional. -/
def affinePushforward' (hg : IsAffineHom B S hS g.hom) : ModuleMapSituation.{u, u} B S hS where
  X := X'
  Y := D.Y
  f := f'
  F := (modulePushforward B S hS g).obj D.F
  G := (modulePushforward B S hS g).obj D.G
  quasicoherent_F :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS g hg D.F
      D.quasicoherent_F
  quasicoherent_G :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS g hg D.G
      D.quasicoherent_G
  u := (modulePushforward B S hS g).map D.u

@[simp]
theorem affinePushforward_Y (h07U8 : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hg : IsAffineHom B S hS g.hom) : (D.affinePushforward g f' h07U8 hg).Y = D.Y := rfl

@[simp]
theorem affinePushforward_Y' (hg : IsAffineHom B S hS g.hom) :
    (D.affinePushforward' g f' hg).Y = D.Y := rfl

/-- The morphism `g_T : X ×_Y T ⟶ X' ×_Y T` of base-change spaces induced by a morphism
`g : X ⟶ X'` over `Y`. -/
def affinePushforwardBaseChange (comm : g ≫ f' = D.f) (T : D.SchemesOver) :
    D.baseChangeSpace T ⟶ AlgebraicSpaces.fiberProduct B S hS f' T.hom :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f' T.hom).lift
    (D.baseChangeProjection T ≫ g) (D.baseChangeInclusion T)
    (by
      rw [Category.assoc, comm]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).w)

/-- **The two inputs that the proof of Stacks 0CW8 imports**, at one test scheme `T`: the
direct image along `g_T` carries the base change `u_T` to the base change `u'_T`, which is the
affine base-change clause of Stacks 07U8; and that direct image reflects and preserves
isomorphisms, monomorphisms, epimorphisms and vanishing at the two modules concerned, which is
how the source uses Stacks 08AI for the affine morphism `g_T`. -/
def PushforwardIdentifiesBaseChange (h07U8 : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (hg : IsAffineHom B S hS g.hom) (comm : g ≫ f' = D.f) (T : D.SchemesOver) : Prop :=
  Nonempty
      (Arrow.mk ((D.affinePushforward g f' h07U8 hg).baseChangeHom
          (modulePullbackSystem B S hS) T) ≅
        Arrow.mk ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T))) ∧
    (IsIso ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T)) ↔
        IsIso (D.baseChangeHom (modulePullbackSystem B S hS) T)) ∧
    (Mono ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T)) ↔
        Mono (D.baseChangeHom (modulePullbackSystem B S hS) T)) ∧
    (Epi ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T)) ↔
        Epi (D.baseChangeHom (modulePullbackSystem B S hS) T)) ∧
    (((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T) = 0) ↔
        D.baseChangeHom (modulePullbackSystem B S hS) T = 0)

/-- **The two inputs that the proof of Stacks 0CW8 imports**, at one test scheme `T`: the
direct image along `g_T` carries the base change `u_T` to the base change `u'_T`, which is the
affine base-change clause of Stacks 07U8; and that direct image reflects and preserves
isomorphisms, monomorphisms, epimorphisms and vanishing at the two modules concerned, which is
how the source uses Stacks 08AI for the affine morphism `g_T`. -/
def PushforwardIdentifiesBaseChange' (hg : IsAffineHom B S hS g.hom)
    (comm : g ≫ f' = D.f) (T : D.SchemesOver) : Prop :=
  Nonempty
      (Arrow.mk ((D.affinePushforward' g f' hg).baseChangeHom
          (modulePullbackSystem B S hS) T) ≅
        Arrow.mk ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T))) ∧
    (IsIso ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T)) ↔
        IsIso (D.baseChangeHom (modulePullbackSystem B S hS) T)) ∧
    (Mono ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T)) ↔
        Mono (D.baseChangeHom (modulePullbackSystem B S hS) T)) ∧
    (Epi ((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T)) ↔
        Epi (D.baseChangeHom (modulePullbackSystem B S hS) T)) ∧
    (((modulePushforward B S hS (D.affinePushforwardBaseChange g f' comm T)).map
          (D.baseChangeHom (modulePullbackSystem B S hS) T) = 0) ↔
        D.baseChangeHom (modulePullbackSystem B S hS) T = 0)

section

variable (h07U8 : SchemeTargetAffinePushforwardQuasicoherent B S hS)
  (hg : IsAffineHom B S hS g.hom) (comm : g ≫ f' = D.f)

/-- **Stacks 0CW8**, pointwise for the isomorphism condition: the base change of `u' = g_*u`
to a test scheme is an isomorphism exactly when the base change of `u` is. -/
theorem isIsoAt_affinePushforward_iff (T : D.SchemesOver)
    (hT : D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).IsIsoAt (modulePullbackSystem B S hS) T ↔
      D.IsIsoAt (modulePullbackSystem B S hS) T :=
  (isIso_iff_of_arrowIso hT.1.some).trans hT.2.1

/-- **Stacks 0CW8**, pointwise for the injectivity condition. -/
theorem isUniversallyInjectiveAt_affinePushforward_iff (T : D.SchemesOver)
    (hT : ∀ T' : D.SchemesOver, D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T') :
    (D.affinePushforward g f' h07U8 hg).IsUniversallyInjectiveAt
        (modulePullbackSystem B S hS) T ↔
      D.IsUniversallyInjectiveAt (modulePullbackSystem B S hS) T :=
  forall_congr' fun T' => forall_congr' fun _ =>
    (mono_iff_of_arrowIso (hT T').1.some).trans (hT T').2.2.1

/-- **Stacks 0CW8**, pointwise for the surjectivity condition. -/
theorem isSurjectiveAt_affinePushforward_iff (T : D.SchemesOver)
    (hT : D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      D.IsSurjectiveAt (modulePullbackSystem B S hS) T :=
  (epi_iff_of_arrowIso hT.1.some).trans hT.2.2.2.1

/-- **Stacks 0CW8**, pointwise for the vanishing condition. -/
theorem isZeroAt_affinePushforward_iff (T : D.SchemesOver)
    (hT : D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).IsZeroAt (modulePullbackSystem B S hS) T ↔
      D.IsZeroAt (modulePullbackSystem B S hS) T :=
  (eq_zero_iff_of_arrowIso hT.1.some).trans hT.2.2.2.2

/-- **Stacks 0CW8**, `F_{u,iso} = F_{u',iso}`. -/
theorem isoFunctor_affinePushforward_eq
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).isoFunctor (modulePullbackSystem B S hS) =
      D.isoFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward g f' h07U8 hg).isIsoAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isIsoAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isIsoAt_affinePushforward_iff g f' h07U8 hg comm T (hT T)

/-- **Stacks 0CW8**, `F_{u,inj} = F_{u',inj}`. -/
theorem injFunctor_affinePushforward_eq
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).injFunctor (modulePullbackSystem B S hS) =
      D.injFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward g f' h07U8 hg).isUniversallyInjectiveAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isUniversallyInjectiveAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isUniversallyInjectiveAt_affinePushforward_iff g f' h07U8 hg comm T hT

/-- **Stacks 0CW8**, `F_{u,surj} = F_{u',surj}`. -/
theorem surjFunctor_affinePushforward_eq
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).surjFunctor (modulePullbackSystem B S hS) =
      D.surjFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward g f' h07U8 hg).isSurjectiveAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isSurjectiveAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isSurjectiveAt_affinePushforward_iff g f' h07U8 hg comm T (hT T)

/-- **Stacks 0CW8**, `F_{u,zero} = F_{u',zero}`. -/
theorem zeroFunctor_affinePushforward_eq
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange g f' h07U8 hg comm T) :
    (D.affinePushforward g f' h07U8 hg).zeroFunctor (modulePullbackSystem B S hS) =
      D.zeroFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward g f' h07U8 hg).isZeroAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isZeroAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isZeroAt_affinePushforward_iff g f' h07U8 hg comm T (hT T)

end

variable (hg : IsAffineHom B S hS g.hom) (comm : g ≫ f' = D.f)

/-- **Stacks 0CW8**, pointwise for the isomorphism condition: the base change of `u' = g_*u`
to a test scheme is an isomorphism exactly when the base change of `u` is. -/
@[stacks 0CW8 "the isomorphism locus, pointwise"]
theorem isIsoAt_affinePushforward_iff' (T : D.SchemesOver)
    (hT : D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).IsIsoAt (modulePullbackSystem B S hS) T ↔
      D.IsIsoAt (modulePullbackSystem B S hS) T :=
  (isIso_iff_of_arrowIso hT.1.some).trans hT.2.1

/-- **Stacks 0CW8**, pointwise for the injectivity condition. -/
@[stacks 0CW8 "the universal-injectivity locus, pointwise"]
theorem isUniversallyInjectiveAt_affinePushforward_iff' (T : D.SchemesOver)
    (hT : ∀ T' : D.SchemesOver, D.PushforwardIdentifiesBaseChange' g f' hg comm T') :
    (D.affinePushforward' g f' hg).IsUniversallyInjectiveAt
        (modulePullbackSystem B S hS) T ↔
      D.IsUniversallyInjectiveAt (modulePullbackSystem B S hS) T :=
  forall_congr' fun T' => forall_congr' fun _ =>
    (mono_iff_of_arrowIso (hT T').1.some).trans (hT T').2.2.1

/-- **Stacks 0CW8**, pointwise for the surjectivity condition. -/
@[stacks 0CW8 "the surjectivity locus, pointwise"]
theorem isSurjectiveAt_affinePushforward_iff' (T : D.SchemesOver)
    (hT : D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      D.IsSurjectiveAt (modulePullbackSystem B S hS) T :=
  (epi_iff_of_arrowIso hT.1.some).trans hT.2.2.2.1

/-- **Stacks 0CW8**, pointwise for the vanishing condition. -/
@[stacks 0CW8 "the vanishing locus, pointwise"]
theorem isZeroAt_affinePushforward_iff' (T : D.SchemesOver)
    (hT : D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).IsZeroAt (modulePullbackSystem B S hS) T ↔
      D.IsZeroAt (modulePullbackSystem B S hS) T :=
  (eq_zero_iff_of_arrowIso hT.1.some).trans hT.2.2.2.2

/-- **Stacks 0CW8**, `F_{u,iso} = F_{u',iso}`. -/
@[stacks 0CW8 "F_iso"]
theorem isoFunctor_affinePushforward_eq'
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).isoFunctor (modulePullbackSystem B S hS) =
      D.isoFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward' g f' hg).isIsoAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isIsoAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isIsoAt_affinePushforward_iff' g f' hg comm T (hT T)

/-- **Stacks 0CW8**, `F_{u,inj} = F_{u',inj}`. -/
@[stacks 0CW8 "F_inj"]
theorem injFunctor_affinePushforward_eq'
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).injFunctor (modulePullbackSystem B S hS) =
      D.injFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward' g f' hg).isUniversallyInjectiveAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isUniversallyInjectiveAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isUniversallyInjectiveAt_affinePushforward_iff' g f' hg comm T hT

/-- **Stacks 0CW8**, `F_{u,surj} = F_{u',surj}`. -/
@[stacks 0CW8 "F_surj"]
theorem surjFunctor_affinePushforward_eq'
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).surjFunctor (modulePullbackSystem B S hS) =
      D.surjFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward' g f' hg).isSurjectiveAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isSurjectiveAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isSurjectiveAt_affinePushforward_iff' g f' hg comm T (hT T)

/-- **Stacks 0CW8**, `F_{u,zero} = F_{u',zero}`. -/
@[stacks 0CW8 "F_zero"]
theorem zeroFunctor_affinePushforward_eq'
    (hT : ∀ T : D.SchemesOver, D.PushforwardIdentifiesBaseChange' g f' hg comm T) :
    (D.affinePushforward' g f' hg).zeroFunctor (modulePullbackSystem B S hS) =
      D.zeroFunctor (modulePullbackSystem B S hS) :=
  subterminalFunctor_congr_of_iff D
    (fun k hQ => (D.affinePushforward' g f' hg).isZeroAt_of_hom
      (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => D.isZeroAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => D.isZeroAt_affinePushforward_iff' g f' hg comm T (hT T)

end ModuleMapSituation

/-! ### Stacks 0CW7: a map whose target is an affine direct image -/

/-- The data of Stacks 0CW7: a morphism `f : X ⟶ Y` of algebraic spaces, an affine morphism
`i : Z ⟶ X`, a quasi-coherent `𝒪_X`-module `F`, a quasi-coherent `𝒪_Z`-module `H`, and a map
`v : i^*F ⟶ H`.

The map `u : F ⟶ i_*H` of the source is the adjoint of `v`, so it is not part of the data;
this keeps the source's identification `G = i_*H` an equality of the two situations' modules
rather than a transport. -/
structure AffineAdjointData where
  /-- The source algebraic space of the morphism of Stacks 083F. -/
  X : AlgebraicSpaces B S hS
  /-- The target algebraic space, over which the test schemes live. -/
  Y : AlgebraicSpaces B S hS
  /-- The algebraic space affine over the source. -/
  Z : AlgebraicSpaces B S hS
  /-- The morphism of Stacks 083F. -/
  f : X ⟶ Y
  /-- The affine morphism presenting the target module as a direct image. -/
  i : Z ⟶ X
  /-- The source module of the map of Stacks 083F. -/
  F : Modules.{u, u} B S hS X.1 X.2
  /-- The module on the affine source whose direct image is the target module. -/
  H : Modules.{u, u} B S hS Z.1 Z.2
  /-- The source module is quasi-coherent. -/
  quasicoherent_F : F.IsQuasicoherentOnSite
  /-- The presenting module is quasi-coherent. -/
  quasicoherent_H : H.IsQuasicoherentOnSite
  /-- The map `v : i^*F ⟶ H` of the lemma. -/
  v : (modulePullback B S hS i).obj F ⟶ H

namespace AffineAdjointData

variable {B S hS} (A : AffineAdjointData.{u} B S hS)

/-- The situation of Stacks 083F carried by the adjoint map `v : i^*F ⟶ H`, over the same
target algebraic space through `i ≫ f`. -/
def adjointSituation
    (hqc : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite) :
    ModuleMapSituation.{u, u} B S hS where
  X := A.Z
  Y := A.Y
  f := A.i ≫ A.f
  F := (modulePullback B S hS A.i).obj A.F
  G := A.H
  quasicoherent_F := hqc
  quasicoherent_G := A.quasicoherent_H
  u := A.v

/-- The situation of Stacks 083F carried by the original map `u : F ⟶ i_*H`, which is the
adjoint of `v`. -/
def sourceSituation
    (hqc : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite) :
    ModuleMapSituation.{u, u} B S hS where
  X := A.X
  Y := A.Y
  f := A.f
  F := A.F
  G := (modulePushforward B S hS A.i).obj A.H
  quasicoherent_F := A.quasicoherent_F
  quasicoherent_G := hqc
  u := (modulePullbackAdjunction B S hS A.i).homEquiv A.F A.H A.v

@[simp]
theorem adjointSituation_Y (hqc : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite) :
    (A.adjointSituation hqc).Y = A.Y := rfl

@[simp]
theorem sourceSituation_Y
    (hqc : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite) :
    (A.sourceSituation hqc).Y = A.Y := rfl

/-- **The input that the proof of Stacks 0CW7 imports**, at one test scheme `T`: the source's
sentence "we see that `u_T` and `v_T` are adjoint maps as well".  Explicitly, there is a
morphism `i_T` of base-change spaces, an identification `a` of `i_T^*(F_T)` with `(i^*F)_T` —
commutation of pullbacks — and an identification `b` of `(i_*H)_T` with `i_{T,*}(H_T)` — the
affine base-change clause of Stacks 07U8 — under which `u_T` is the adjoint of `v_T`. -/
def IsAdjointAfterBaseChange
    (hqcF : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite)
    (hqcH : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite)
    (T : (A.sourceSituation hqcH).SchemesOver)
    (iT : (A.adjointSituation hqcF).baseChangeSpace T ⟶
      (A.sourceSituation hqcH).baseChangeSpace T) : Prop :=
  ∃ (a : (modulePullback B S hS iT).obj
          ((modulePullback B S hS ((A.sourceSituation hqcH).baseChangeProjection T)).obj A.F) ≅
        (modulePullback B S hS ((A.adjointSituation hqcF).baseChangeProjection T)).obj
          ((modulePullback B S hS A.i).obj A.F))
    (b : (modulePullback B S hS ((A.sourceSituation hqcH).baseChangeProjection T)).obj
          ((modulePushforward B S hS A.i).obj A.H) ≅
        (modulePushforward B S hS iT).obj
          ((modulePullback B S hS ((A.adjointSituation hqcF).baseChangeProjection T)).obj A.H)),
    (A.sourceSituation hqcH).baseChangeHom (modulePullbackSystem B S hS) T ≫ b.hom =
      (modulePullbackAdjunction B S hS iT).homEquiv _ _
        (a.hom ≫ (A.adjointSituation hqcF).baseChangeHom (modulePullbackSystem B S hS) T)

/-- **The input that the proof of Stacks 0CW7 imports**, at one test scheme: some morphism of
base-change spaces exhibits `u_T` as the adjoint of `v_T`. -/
def AdjointAfterBaseChange
    (hqcF : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite)
    (hqcH : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite)
    (T : (A.sourceSituation hqcH).SchemesOver) : Prop :=
  ∃ iT : (A.adjointSituation hqcF).baseChangeSpace T ⟶
      (A.sourceSituation hqcH).baseChangeSpace T,
    A.IsAdjointAfterBaseChange hqcF hqcH T iT

variable (hqcF : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite)
  (hqcH : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite)

/-- **Stacks 0CW7, part (1)**, pointwise: the base change of `u` to a test scheme vanishes
exactly when the base change of its adjoint `v` does.

An adjunction between preadditive categories whose right adjoint is additive carries `0` to
`0` and is a bijection, so it carries nothing else to `0`. -/
@[stacks 0CW7 "part (1), pointwise"]
theorem isZeroAt_adjointSituation_iff (T : (A.sourceSituation hqcH).SchemesOver)
    (hT : A.AdjointAfterBaseChange hqcF hqcH T) :
    (A.adjointSituation hqcF).IsZeroAt (modulePullbackSystem B S hS) T ↔
      (A.sourceSituation hqcH).IsZeroAt (modulePullbackSystem B S hS) T := by
  obtain ⟨iT, a, b, hadj⟩ := hT
  have := (modulePullbackAdjunction B S hS iT).isRightAdjoint
  set w := (A.adjointSituation hqcF).baseChangeHom (modulePullbackSystem B S hS) T
  set z := (A.sourceSituation hqcH).baseChangeHom (modulePullbackSystem B S hS) T
  have hequiv : (modulePullbackAdjunction B S hS iT).homEquiv _ _ (a.hom ≫ w) = 0 ↔
      a.hom ≫ w = 0 := by
    constructor
    · intro hx
      refine (modulePullbackAdjunction B S hS iT).homEquiv _ _ |>.injective ?_
      rw [hx, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero]
    · intro hx
      rw [hx, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero]
  constructor
  · intro h
    have hwz : w = 0 := h
    have haw : a.hom ≫ w = 0 :=
      (congrArg (fun t => a.hom ≫ t) hwz).trans comp_zero
    have hzb : z ≫ b.hom = 0 := hadj.trans (hequiv.2 haw)
    exact (Iso.cancel_iso_hom_right _ _ b).1 (hzb.trans zero_comp.symm)
  · intro h
    have hz0 : z = 0 := h
    have hzb : z ≫ b.hom = 0 :=
      (congrArg (fun t => t ≫ b.hom) hz0).trans zero_comp
    have haw : a.hom ≫ w = 0 := hequiv.1 (hadj.symm.trans hzb)
    exact (Iso.cancel_iso_hom_left a _ _).1 (haw.trans comp_zero.symm)

/-- **Stacks 0CW7, part (1)**: `F_{v,zero} = F_{u,zero}`. -/
@[stacks 0CW7 "part (1)"]
theorem zeroFunctor_adjointSituation_eq
    (hT : ∀ T : (A.sourceSituation hqcH).SchemesOver, A.AdjointAfterBaseChange hqcF hqcH T) :
    (A.adjointSituation hqcF).zeroFunctor (modulePullbackSystem B S hS) =
      (A.sourceSituation hqcH).zeroFunctor (modulePullbackSystem B S hS) :=
  ModuleMapSituation.subterminalFunctor_congr_of_iff (A.sourceSituation hqcH)
    (fun k hQ => (A.adjointSituation hqcF).isZeroAt_of_hom (modulePullbackSystem B S hS) k hQ)
    (fun k hQ => (A.sourceSituation hqcH).isZeroAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => A.isZeroAt_adjointSituation_iff hqcF hqcH T (hT T)

/-- **The extra input that part (2) of the proof of Stacks 0CW7 imports** at one test scheme,
for a closed immersion `i`: the base change `i_T` is again a closed immersion (Stacks 03WI for
closed immersions), the unit `F_T ⟶ i_{T,*}i_T^*F_T` is surjective (Stacks 04CJ, part (1)),
and `i_{T,*}` preserves surjections (the exactness assertion of Stacks 04CJ, part (3), which
this repository does not carry). -/
def ClosedImmersionSurjectivityInput
    (hqcF : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite)
    (hqcH : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite)
    (T : (A.sourceSituation hqcH).SchemesOver)
    (iT : (A.adjointSituation hqcF).baseChangeSpace T ⟶
      (A.sourceSituation hqcH).baseChangeSpace T) : Prop :=
  IsClosedImmersion B S hS iT.hom ∧
    Epi ((modulePullbackAdjunction B S hS iT).unit.app
      ((modulePullback B S hS ((A.sourceSituation hqcH).baseChangeProjection T)).obj A.F)) ∧
    (modulePushforward B S hS iT).PreservesEpimorphisms

/-- **Stacks 0CW7, part (2)**, pointwise: for a closed immersion, the base change of `u` to a
test scheme is surjective exactly when the base change of its adjoint `v` is.

Forward, the factorisation `u_T = unit ≫ i_{T,*}(v_T)` makes `i_{T,*}(v_T)` an epimorphism,
and the direct image along a closed immersion is fully faithful
(`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`), hence faithful, hence reflects
epimorphisms.  Backward, the unit is an epimorphism and the direct image preserves them. -/
@[stacks 0CW7 "part (2), pointwise"]
theorem isSurjectiveAt_adjointSituation_iff (T : (A.sourceSituation hqcH).SchemesOver)
    (hT : ∃ iT : (A.adjointSituation hqcF).baseChangeSpace T ⟶
        (A.sourceSituation hqcH).baseChangeSpace T,
      A.IsAdjointAfterBaseChange hqcF hqcH T iT ∧
        A.ClosedImmersionSurjectivityInput hqcF hqcH T iT) :
    (A.adjointSituation hqcF).IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      (A.sourceSituation hqcH).IsSurjectiveAt (modulePullbackSystem B S hS) T := by
  obtain ⟨iT, ⟨a, b, hadj⟩, hiT, hunit, hpres⟩ := hT
  set w := (A.adjointSituation hqcF).baseChangeHom (modulePullbackSystem B S hS) T
  set z := (A.sourceSituation hqcH).baseChangeHom (modulePullbackSystem B S hS) T
  have hfaithful : (modulePushforward B S hS iT).Faithful :=
    (fullyFaithfulModulePushforward B S hS iT hiT).faithful
  have hpresEpi := hpres
  have hfactor : z ≫ b.hom =
      (modulePullbackAdjunction B S hS iT).unit.app _ ≫
        (modulePushforward B S hS iT).map (a.hom ≫ w) := by
    rw [hadj, Adjunction.homEquiv_apply]
  have h4 : Epi (z ≫ b.hom) ↔ Epi z :=
    @epi_comp_iff_of_isIso _ _ _ _ _ z b.hom (Iso.isIso_hom b)
  have h3 : Epi ((modulePushforward B S hS iT).map (a.hom ≫ w)) ↔ Epi (z ≫ b.hom) := by
    rw [hfactor]
    exact (@epi_comp_iff_of_epi _ _ _ _ _ _ hunit _).symm
  have h2 : Epi (a.hom ≫ w) ↔ Epi ((modulePushforward B S hS iT).map (a.hom ≫ w)) :=
    (Functor.epi_map_iff_epi (modulePushforward B S hS iT) (a.hom ≫ w)).symm
  have : Epi a.hom := @IsIso.epi_of_iso _ _ _ _ a.hom (Iso.isIso_hom a)
  have h1 : Epi w ↔ Epi (a.hom ≫ w) := (epi_comp_iff_of_epi a.hom w).symm
  exact h1.trans (h2.trans (h3.trans h4))

/-- **Stacks 0CW7, part (2)**: for a closed immersion, `F_{v,surj} = F_{u,surj}`. -/
@[stacks 0CW7 "part (2)"]
theorem surjFunctor_adjointSituation_eq
    (hT : ∀ T : (A.sourceSituation hqcH).SchemesOver,
      ∃ iT : (A.adjointSituation hqcF).baseChangeSpace T ⟶
          (A.sourceSituation hqcH).baseChangeSpace T,
        A.IsAdjointAfterBaseChange hqcF hqcH T iT ∧
          A.ClosedImmersionSurjectivityInput hqcF hqcH T iT) :
    (A.adjointSituation hqcF).surjFunctor (modulePullbackSystem B S hS) =
      (A.sourceSituation hqcH).surjFunctor (modulePullbackSystem B S hS) :=
  ModuleMapSituation.subterminalFunctor_congr_of_iff (A.sourceSituation hqcH)
    (fun k hQ =>
      (A.adjointSituation hqcF).isSurjectiveAt_of_hom (modulePullbackSystem B S hS) k hQ)
    (fun k hQ =>
      (A.sourceSituation hqcH).isSurjectiveAt_of_hom (modulePullbackSystem B S hS) k hQ)
    fun T => A.isSurjectiveAt_adjointSituation_iff hqcF hqcH T (hT T)

end AffineAdjointData

end AlgebraicGeometry.Space

end
