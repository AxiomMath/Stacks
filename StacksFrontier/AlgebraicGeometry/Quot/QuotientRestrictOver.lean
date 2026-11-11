module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorDescent
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits

/-!
# Restriction of a quotient of an inverse image along a morphism over the base

The machinery the fpqc sheaf property of the functor of quotients in the source (Stacks 08IV) is
written with, independently of Situation 082M: the transport of a quotient along an isomorphism,
the restriction `AlgebraicGeometry.Space.quotientRestrictOver` of a quotient of `a^*F` along a
morphism over `X`, the base change `AlgebraicGeometry.Space.baseChangeAlong` of a morphism of
algebraic spaces over `Y`, and the predicates naming the descent inputs that
`StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean` proves.

A quotient of `a^*F` for `a : W ⟶ X` is recorded by its kernel, a subobject `K` of `a^*F`, as in
Situation 082M; for `a' = g ≫ a` its restriction along `g` is the quotient
`a'^*F ≅ g^*a^*F ⟶ g^*(a^*F/K)`, recorded in the same way.  Recording it as a subobject of the
*single* inverse image `a'^*F`, rather than as an iterated inverse image, is what makes
restriction transitive on the nose
(`AlgebraicGeometry.Space.quotientRestrictOver_comp`), hence what makes the diagram of
Stacks 08IV commute.

## Main definitions

* `CategoryTheory.Limits.quotientTransport`: the transport of a quotient of an object along an
  isomorphism with another object, recorded — as the quotients of Situation 082M are — by its
  kernel.
* `AlgebraicGeometry.Space.quotientRestrictOver`: the restriction of a quotient of `a^*F` along
  a morphism `g : W' ⟶ W` over `X`, a subobject of `a'^*F` for `a' = g ≫ a`.  This is
  `AlgebraicGeometry.Space.quotientRestrict` of Stacks 08IU read through the canonical
  identification `a'^*F ≅ g^*a^*F` of Stacks 03LU.
* `AlgebraicGeometry.Space.baseChangeAlong`: the base change `W'_T ⟶ W_T` of a morphism
  `W' ⟶ W` of algebraic spaces over `Y`.
* `AlgebraicGeometry.Space.PullbackPreservesQuasicoherenceEverywhere`,
  `AlgebraicGeometry.Space.KernelQuasicoherent`,
  `AlgebraicGeometry.Space.FlatOverPullbackOver`,
  `AlgebraicGeometry.Space.FlatOverDescendsAlongFpqcCovering`,
  `AlgebraicGeometry.Space.FinitePresentationOnSiteDescendsAlongFpqcCovering` and
  `AlgebraicGeometry.Space.DescendsQuotientsAlongFpqcCovering`: the descent inputs of
  Stacks 08IV, named as predicates so that they can be stated here and proved in
  `StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean`.

## Main results

* `AlgebraicGeometry.Space.quotientRestrictOver_comp`: restriction of a quotient over `X` is
  transitive.
* `AlgebraicGeometry.Space.eq_of_quotientRestrictOver_eq`: restriction of a quotient over `X`
  along an fpqc covering is injective.
* `AlgebraicGeometry.Space.isFpqcCovering_baseChangeAlong`: the base change to `T` of an fpqc
  covering is an fpqc covering, which is what carries a covering of the source over to the base
  changes where the quotients of Situation 082M live.

## References

* [Stacks Project, Tag 08IV](https://stacks.math.columbia.edu/tag/08IV)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace CategoryTheory.Limits

namespace QuotientTransport

variable {C : Type*} [Category* C] [Abelian C]

/-! ### Transport of a quotient along an isomorphism -/

/-- **The transport of a quotient along an isomorphism `ι : A' ≅ A`.**  A quotient of `A` is
recorded by its kernel, a subobject `K` of `A`, the quotient itself being `A/K`; its transport
is the quotient `A' ≅ A ⟶ A/K` of `A'`, recorded in the same way by its kernel.

This is the identification of the quotients of two isomorphic objects, written so that it
composes with `AlgebraicGeometry.Space.quotientRestrict`: both are the kernel subobject of a
composite ending in the projection onto a quotient. -/
def quotientTransport {A A' : C} (ι : A' ≅ A) (K : Subobject A) : Subobject A' :=
  kernelSubobject (ι.hom ≫ cokernel.π K.arrow)

/-- **The quotient by the transported subobject is the original quotient.** -/
def quotientTransportCokernelIso {A A' : C} (ι : A' ≅ A) (K : Subobject A) :
    cokernel (quotientTransport ι K).arrow ≅ cokernel K.arrow :=
  Abelian.cokernelKernelSubobjectIso (ι.hom ≫ cokernel.π K.arrow)

/-- The projection onto the quotient by the transported subobject is the transported
projection, read through `CategoryTheory.Limits.quotientTransportCokernelIso`. -/
theorem comp_quotientTransportCokernelIso_inv {A A' : C} (ι : A' ≅ A) (K : Subobject A) :
    (ι.hom ≫ cokernel.π K.arrow) ≫ (quotientTransportCokernelIso ι K).inv =
      cokernel.π (quotientTransport ι K).arrow :=
  Abelian.cokernelKernelSubobjectIso_inv_comp (ι.hom ≫ cokernel.π K.arrow)

/-- Transporting along the identity does nothing. -/
@[simp]
theorem quotientTransport_refl {A : C} (K : Subobject A) :
    quotientTransport (Iso.refl A) K = K :=
  (kernelSubobject_eq_of_comp_mono (cokernel.π K.arrow)
    ((Iso.refl A).hom ≫ cokernel.π K.arrow) (𝟙 (cokernel K.arrow))
    (by rw [Category.comp_id, Iso.refl_hom, Category.id_comp])).trans
    (kernelSubobject_cokernel_π K)

/-- Transport of quotients is compatible with composition of isomorphisms. -/
theorem quotientTransport_trans {A A' A'' : C} (ι : A' ≅ A) (ι' : A'' ≅ A')
    (K : Subobject A) :
    quotientTransport ι' (quotientTransport ι K) = quotientTransport (ι' ≪≫ ι) K :=
  kernelSubobject_eq_of_comp_mono ((ι' ≪≫ ι).hom ≫ cokernel.π K.arrow)
    (ι'.hom ≫ cokernel.π (quotientTransport ι K).arrow)
    (quotientTransportCokernelIso ι K).inv
    (by rw [← comp_quotientTransportCokernelIso_inv ι K]; simp)

/-- Transporting along an isomorphism and then back along its inverse does nothing. -/
@[simp]
theorem quotientTransport_symm_quotientTransport {A A' : C} (ι : A' ≅ A) (K : Subobject A) :
    quotientTransport ι.symm (quotientTransport ι K) = K := by
  rw [quotientTransport_trans, Iso.symm_self_id, quotientTransport_refl]

/-- Transport of quotients along an isomorphism is injective. -/
theorem quotientTransport_injective {A A' : C} (ι : A' ≅ A) :
    Function.Injective (quotientTransport ι) :=
  Function.LeftInverse.injective (quotientTransport_symm_quotientTransport ι)

end QuotientTransport

/- These re-exports keep the declarations above reachable under the names they carried while they
lived in `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSourceSheaf.lean`, which imports this
file so that the proofs of the descent inputs of Stacks 08IV can be stated before it. -/
export CategoryTheory.Limits.QuotientTransport (comp_quotientTransportCokernelIso_inv
  quotientTransport quotientTransportCokernelIso
  quotientTransport_injective
  quotientTransport_refl
  quotientTransport_symm_quotientTransport
  quotientTransport_trans)

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace RestrictOver

open CategoryTheory.Limits.QuotientTransport

/-! ### Restriction of a quotient of an inverse image along a morphism over the base -/

/-- **The restriction of a quotient of `a^*F` along a morphism `g : W' ⟶ W` over `X`.**  A
quotient of the inverse image of `F` along `a : W ⟶ X` is recorded by its kernel, a subobject
`K` of `a^*F`, the quotient itself being `a^*F/K`; for `a' = g ≫ a` its restriction along `g` is
the quotient `a'^*F ≅ g^*a^*F ⟶ g^*(a^*F/K)` of `a'^*F`, recorded in the same way by its kernel,
the first map being the comparison of Stacks 03LU.

This is `AlgebraicGeometry.Space.quotientRestrict` of Stacks 08IU normalised so that the
quotient on each node of a covering diagram is a subobject of a *single* inverse image of `F`;
that is what makes restriction transitive on the nose, which is
`AlgebraicGeometry.Space.quotientRestrictOver_comp`. -/
def quotientRestrictOver {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X} {a' : W' ⟶ X}
    (g : W' ⟶ W) (h : g ≫ a = a') (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS a).obj F)) :
    Subobject ((modulePullback B S hS a').obj F) :=
  Functor.conjSubobject (modulePullbackTriangle B S hS h) K

/-- **The quotient by the restricted subobject is the inverse image of the quotient.** -/
def quotientRestrictOverCokernelIso {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X}
    {a' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ a = a') (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS a).obj F)) :
    cokernel (quotientRestrictOver g h F K).arrow ≅
      (modulePullback B S hS g).obj (cokernel K.arrow) :=
  Functor.conjSubobjectCokernelIso (modulePullbackTriangle B S hS h) K

/-- Restriction over `X` is restriction in the sense of Stacks 08IU, transported along the
comparison of Stacks 03LU.  This is what carries the injectivity of Stacks 08IU over to the
normalised restriction maps. -/
theorem quotientRestrictOver_eq_quotientTransport {X W W' : AlgebraicSpaces B S hS}
    {a : W ⟶ X} {a' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ a = a')
    (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS a).obj F)) :
    quotientRestrictOver g h F K =
      quotientTransport ((modulePullbackTriangle B S hS h).app F) (quotientRestrict g K) :=
  (kernelSubobject_eq_of_comp_mono
    ((modulePullbackTriangle B S hS h).hom.app F ≫
      (modulePullback B S hS g).map (cokernel.π K.arrow))
    (((modulePullbackTriangle B S hS h).app F).hom ≫
      cokernel.π (quotientRestrict g K).arrow)
    (quotientRestrictCokernelIso g K).inv
    (by rw [Category.assoc, cokernel_π_comp_quotientRestrictCokernelIso_inv]; rfl)).symm

/-- **Restriction of a quotient over `X` is transitive.**  Restricting along `g` and then along
`g'` is restricting along a morphism equal to the composite.

This is the associativity coherence of the comparison of inverse images of Stacks 03LU, which
is why it carries `AlgebraicGeometry.Space.ModulePushforwardCoherence`. -/
theorem quotientRestrictOver_comp (hc : ModulePushforwardCoherence B S hS)
    {X W W' W'' : AlgebraicSpaces B S hS} {a : W ⟶ X} {a' : W' ⟶ X} {a'' : W'' ⟶ X}
    {g : W' ⟶ W} {g' : W'' ⟶ W'} {k : W'' ⟶ W} (hk : g' ≫ g = k) (h₂ : g ≫ a = a')
    (h₁ : g' ≫ a' = a'') (h₃ : k ≫ a = a'') (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS a).obj F)) :
    quotientRestrictOver g' h₁ F (quotientRestrictOver g h₂ F K) =
      quotientRestrictOver k h₃ F K :=
  (Functor.conjSubobject_comp (modulePullbackTriangle B S hS h₂)
    (modulePullbackTriangle B S hS h₁) (modulePullbackTriangle B S hS h₃)
    (modulePullbackTriangle B S hS hk)
    (hc.modulePullbackTriangle_comp' hk h₂ h₁ h₃) K).symm

/-- **A quotient over `X` is determined by its restrictions along an fpqc covering.**  This is
the injectivity half of Stacks 08IU, read for the normalised restriction maps: two quotients of
`a^*F` with quasi-coherent kernel and quasi-coherent quotient whose restrictions along the
members of an fpqc covering of `W` agree are equal.

The faithfulness clause of Stacks 04W8 is no longer needed: it is discharged by
`AlgebraicGeometry.Space.reflectsZeroAlongFpqcCovering`, which
`AlgebraicGeometry.Space.eq_of_quotientRestrict_eq` now applies itself.  The argument of that
type is kept, unused, so that the chain of statements that threads it need not change. -/
theorem eq_of_quotientRestrictOver_eq (_hfaith : ReflectsZeroAlongFpqcCovering.{u, v} B S hS)
    {I : Type v} {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    {a : W ⟶ X} {aZ : ∀ i, Z i ⟶ X} (p : ∀ i, Z i ⟶ W) (hp : ∀ i, p i ≫ a = aZ i)
    (hcov : IsFpqcCovering B S hS fun i ↦ (p i).hom) (F : Modules.{u, u} B S hS X.1 X.2)
    {K K' : Subobject ((modulePullback B S hS a).obj F)}
    (hK : (K : Modules.{u, u} B S hS W.1 W.2).IsQuasicoherentOnSite)
    (hK' : (K' : Modules.{u, u} B S hS W.1 W.2).IsQuasicoherentOnSite)
    (hQ : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hQ' : (cokernel K'.arrow).IsQuasicoherentOnSite)
    (h : ∀ i, quotientRestrictOver (p i) (hp i) F K =
      quotientRestrictOver (p i) (hp i) F K') :
    K = K' := by
  refine eq_of_quotientRestrict_eq p hcov hK hK' hQ hQ' fun i ↦ ?_
  refine quotientTransport_injective ((modulePullbackTriangle B S hS (hp i)).app F) ?_
  rw [← quotientRestrictOver_eq_quotientTransport, ← quotientRestrictOver_eq_quotientTransport]
  exact h i

/-! ### Base change of a morphism of algebraic spaces over the base -/

section BaseChangeAlong

variable {Y W W' W'' : AlgebraicSpaces B S hS}

/-- **The base change of a morphism over `Y`.**  For morphisms `a : W ⟶ Y` and `a' : W' ⟶ Y`
and `b : W' ⟶ W` with `b ≫ a = a'`, the induced morphism `W'_T = W' ×_Y T ⟶ W ×_Y T = W_T` of
base changes to a test scheme `T` over `Y`. -/
def baseChangeAlong {a : W ⟶ Y} {a' : W' ⟶ Y} (b : W' ⟶ W) (hb : b ≫ a = a')
    (T : SchemesOver Y) : baseChangeSpace a' T ⟶ baseChangeSpace a T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS a T.hom).lift
    (baseChangeProjection a' T ≫ b) (baseChangeInclusion a' T) <| by
      rw [Category.assoc, hb]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS a' T.hom).w

/-- The base change of a morphism over `Y` commutes with the projections to the sources. -/
@[reassoc (attr := simp)]
theorem baseChangeAlong_comp_projection {a : W ⟶ Y} {a' : W' ⟶ Y} (b : W' ⟶ W)
    (hb : b ≫ a = a') (T : SchemesOver Y) :
    baseChangeAlong b hb T ≫ baseChangeProjection a T = baseChangeProjection a' T ≫ b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS a T.hom).lift_fst _ _ _

/-- The base change of a morphism over `Y` commutes with the projections to the test
scheme. -/
@[reassoc (attr := simp)]
theorem baseChangeAlong_comp_inclusion {a : W ⟶ Y} {a' : W' ⟶ Y} (b : W' ⟶ W)
    (hb : b ≫ a = a') (T : SchemesOver Y) :
    baseChangeAlong b hb T ≫ baseChangeInclusion a T = baseChangeInclusion a' T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS a T.hom).lift_snd _ _ _

/-- Base change of morphisms over `Y` is compatible with composition. -/
theorem baseChangeAlong_comp {a : W ⟶ Y} {a' : W' ⟶ Y} {a'' : W'' ⟶ Y} {b : W' ⟶ W}
    {b' : W'' ⟶ W'} {d : W'' ⟶ W} (hd : b' ≫ b = d) (hb : b ≫ a = a')
    (hb' : b' ≫ a' = a'') (hd' : d ≫ a = a'') (T : SchemesOver Y) :
    baseChangeAlong b' hb' T ≫ baseChangeAlong b hb T = baseChangeAlong d hd' T := by
  subst hd
  refine baseChange_hom_ext a ?_ ?_ <;> simp

/-- **The base change of a morphism over `Y` is cartesian**: the square formed by the morphism
of base changes, the morphism itself and the two projections to the sources is cartesian. -/
theorem isPullback_baseChangeAlong {a : W ⟶ Y} {a' : W' ⟶ Y} (b : W' ⟶ W) (hb : b ≫ a = a')
    (T : SchemesOver Y) :
    IsPullback (baseChangeProjection a' T) (baseChangeAlong b hb T) b
      (baseChangeProjection a T) := by
  have hs : IsPullback (baseChangeAlong b hb T ≫ baseChangeInclusion a T)
      (baseChangeProjection a' T) T.hom (b ≫ a) := by
    rw [baseChangeAlong_comp_inclusion, hb]
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS a' T.hom).flip
  exact (IsPullback.of_right hs (baseChangeAlong_comp_projection b hb T)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS a T.hom).flip).flip

/-- **The base change of a cartesian square over `Y` is cartesian.**  If `c₁, c₂` exhibit `P` as
the fibre product of `b₁ : W₁ ⟶ X` and `b₂ : W₂ ⟶ X`, then their base changes exhibit `P_T` as
the fibre product of `W₁,T` and `W₂,T` over `X_T`. -/
theorem isPullback_baseChangeAlong_pair {X : AlgebraicSpaces B S hS} (u : X ⟶ Y)
    {W₁ W₂ P : AlgebraicSpaces B S hS} {b₁ : W₁ ⟶ X} {b₂ : W₂ ⟶ X} {c₁ : P ⟶ W₁}
    {c₂ : P ⟶ W₂} {d : P ⟶ X} (hP : IsPullback c₁ c₂ b₁ b₂) (hd₁ : c₁ ≫ b₁ = d)
    (hd₂ : c₂ ≫ b₂ = d) (h₁ : c₁ ≫ (b₁ ≫ u) = d ≫ u) (h₂ : c₂ ≫ (b₂ ≫ u) = d ≫ u)
    (T : SchemesOver Y) :
    IsPullback (baseChangeAlong c₁ h₁ T) (baseChangeAlong c₂ h₂ T)
      (baseChangeAlong b₁ (rfl : b₁ ≫ u = b₁ ≫ u) T)
      (baseChangeAlong b₂ (rfl : b₂ ≫ u = b₂ ≫ u) T) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_baseChangeAlong b₁ rfl T)
  · rw [baseChangeAlong_comp_projection c₁ h₁ T, baseChangeAlong_comp_projection b₂ rfl T]
    exact (isPullback_baseChangeAlong c₂ h₂ T).paste_horiz hP
  · rw [baseChangeAlong_comp hd₁ rfl h₁ rfl T, baseChangeAlong_comp hd₂ rfl h₂ rfl T]

/-- **The base change of an fpqc covering is an fpqc covering.**  If `{b i : W' i ⟶ W}` is an
fpqc covering of algebraic spaces over `Y`, then so is the family of base changes
`{W' i ×_Y T ⟶ W ×_Y T}`.

Flatness of the base change is Stacks 03MO,
`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`; the affine refinements of Stacks 03MQ
are carried over by the universal property of the base change. -/
theorem isFpqcCovering_baseChangeAlong {a : W ⟶ Y} {I : Type v}
    {W' : I → AlgebraicSpaces B S hS} {a' : ∀ i, W' i ⟶ Y} (b : ∀ i, W' i ⟶ W)
    (hb : ∀ i, b i ≫ a = a' i) (hcov : IsFpqcCovering B S hS fun i ↦ (b i).hom)
    (T : SchemesOver Y) :
    IsFpqcCovering B S hS fun i ↦ (baseChangeAlong (b i) (hb i) T).hom := by
  refine ⟨fun i ↦ (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_baseChangeAlong (b i) (hb i) T) (hcov.1 i), fun T₀ h ↦ ?_⟩
  obtain ⟨U, hfin, hmem, hrefine⟩ := hcov.2 T₀ (h ≫ (baseChangeProjection a T).hom)
  refine ⟨U, hfin, hmem, fun j ↦ ?_⟩
  obtain ⟨i, α, hα⟩ := hrefine j
  have hhom : ∀ {V V' : AlgebraicSpaces B S hS} {m m' : V ⟶ V'}, m = m' → m.hom = m'.hom :=
    fun hm ↦ by rw [hm]
  have hlift := (isPullback_baseChangeAlong (b i) (hb i) T).lift_snd
    (ObjectProperty.homMk α :
      (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (U.X j)) ⟶ W' i)
    (ObjectProperty.homMk
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)) ≫ h))
    (ObjectProperty.hom_ext _ (hα.trans (Category.assoc _ _ _).symm))
  exact ⟨i, _, hhom hlift⟩

end BaseChangeAlong

/-! ### The inputs this development does not carry -/

/-- **Stacks 03GA at every morphism of algebraic spaces**, reduced as in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean` to the
inverse-image factor of the quasi-coherent clause of Stacks 03DO, carried as a hypothesis: the
inverse image along any morphism preserves quasi-coherence. -/
def PullbackPreservesQuasicoherenceEverywhere (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {V W : AlgebraicSpaces B S hS} (g : V ⟶ W), HasLocalInverseImagePresentations B S hS g

/-- **The kernel clause of Stacks 03DO for quasi-coherence on the small étale site**, as a named
predicate: the kernel of a quotient of a quasi-coherent module whose quotient module is
quasi-coherent is itself quasi-coherent.

This is the hypothesis `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorDescent.lean` states
pointwise in the signatures of its main results; it is needed because the injectivity of
Stacks 08IU applies the faithfulness clause of Stacks 04W8 to a homomorphism whose source is
the kernel.  It is proved as `AlgebraicGeometry.Space.kernelQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean`. -/
def KernelQuasicoherent (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {W : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS W.1 W.2),
    M.IsQuasicoherentOnSite → ∀ K : Subobject M, (cokernel K.arrow).IsQuasicoherentOnSite →
      (K : Modules.{u, u} B S hS W.1 W.2).IsQuasicoherentOnSite

/-- **Stacks 05VW for a morphism over the base**, carried as a hypothesis: the inverse image
along a morphism `g : V ⟶ W` over `Z` of a module on `W` flat over `Z` is flat over `Z`.

This is what `AlgebraicGeometry.Space.QuotientSituation.PullbackPreservesFlatOver` says for the
base-change maps of Situation 082M, here for the morphisms of base changes that the covering of
the source produces — and with no quasi-coherence assumption on the module, which is why it is
carried rather than proved. -/
def FlatOverPullbackOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {V W Z : AlgebraicSpaces B S hS} {w : W ⟶ Z} {v : V ⟶ Z} (g : V ⟶ W), g ≫ w = v →
    ∀ M : Modules.{u, u} B S hS W.1 W.2, IsFlatOver B S hS W.2 w.hom M →
      IsFlatOver B S hS V.2 v.hom ((modulePullback B S hS g).obj M)

/-- **Stacks 05VY for modules along a jointly surjective flat family**, carried as a
hypothesis: a quasi-coherent module on `W` whose inverse image along every member of an fpqc
covering of `W` is flat over `Z` is itself flat over `Z`.

Only the structure-sheaf case of Stacks 05VY is available in this development, as
`AlgebraicGeometry.Space.isFlat_of_comp_of_isSurjective_of_isFlat`; it is a statement about the
flatness of a morphism and does not mention a module, so it cannot discharge this. -/
def FlatOverDescendsAlongFpqcCovering (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {I : Type v} {W Z : AlgebraicSpaces B S hS} {V : I → AlgebraicSpaces B S hS}
    {w : W ⟶ Z} {v : ∀ i, V i ⟶ Z} (p : ∀ i, V i ⟶ W), (∀ i, p i ≫ w = v i) →
    IsFpqcCovering B S hS (fun i ↦ (p i).hom) →
    ∀ M : Modules.{u, u} B S hS W.1 W.2, M.IsQuasicoherentOnSite →
      (∀ i, IsFlatOver B S hS (V i).2 (v i).hom ((modulePullback B S hS (p i)).obj M)) →
        IsFlatOver B S hS W.2 w.hom M

/-- **Stacks 060V for `SheafOfModules.IsFinitePresentationOnSite`**, carried as a hypothesis: a
quasi-coherent module whose inverse image along every member of an fpqc covering is of finite
presentation on the site is itself of finite presentation on the site.

Stacks 060V is available in this development, as
`AlgebraicGeometry.Space.isFinitePresentation_of_modulePullback_fpqcCovering`, but for
Mathlib's `SheafOfModules.IsFinitePresentation`.  That predicate and
`SheafOfModules.IsFinitePresentationOnSite`, which is the one the subfunctor `Q^{fp}` of
Situation 082M is cut out by, are both Stacks 03DL part (7), and no comparison between them is
available here; this is therefore carried rather than deduced. -/
def FinitePresentationOnSiteDescendsAlongFpqcCovering (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {I : Type v} {W : AlgebraicSpaces B S hS} {V : I → AlgebraicSpaces B S hS}
    (p : ∀ i, V i ⟶ W), IsFpqcCovering B S hS (fun i ↦ (p i).hom) →
    ∀ M : Modules.{u, u} B S hS W.1 W.2, M.IsQuasicoherentOnSite →
      (∀ i, ((modulePullback B S hS (p i)).obj M).IsFinitePresentationOnSite) →
        M.IsFinitePresentationOnSite

/-- **The surjectivity half of the bijection of Stacks 08IU, read over a base**, as a named
predicate: for an fpqc covering `{p i : Z i ⟶ W}` of algebraic spaces over `X`
and a quasi-coherent module `a^*F` on `W`, a family of quotients of the `aZ i ^*F` with
quasi-coherent quotient modules which agree on the fibre products `Z i ×_W Z j` is the family of
restrictions of a quotient of `a^*F` with quasi-coherent quotient module.

This is the fullness and the effectivity clauses of the fpqc descent of quasi-coherent modules,
Stacks 04W8, together with the fpqc locality of surjectivity of a homomorphism, which is the
last paragraph of Stacks 08IU.  The predicate asks for no quasi-coherence of `F` itself; when
`a^*F` is quasi-coherent, as in Stacks 08IU, its conclusion is
`AlgebraicGeometry.Space.descendsQuotientsAlongFpqcCovering_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientDescentClauses.lean`, and the bijection itself is
`AlgebraicGeometry.Space.bijOn_quotientRestrict_of_isFpqcCovering`.

The agreement condition is asked for on the fibre products, in the shape a descent datum has,
and *not* on the members of a refining covering: upgrading agreement on a refining covering to
agreement on the fibre product is the step of Stacks 08IU that consumes the refining coverings
of Stacks 08IV, and it is proved below rather than assumed. -/
def DescendsQuotientsAlongFpqcCovering (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ {I : Type v} {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    {P : I → I → AlgebraicSpaces B S hS} {a : W ⟶ X} {aZ : ∀ i, Z i ⟶ X}
    {aP : ∀ i j, P i j ⟶ X} (p : ∀ i, Z i ⟶ W) (r₀ : ∀ i j, P i j ⟶ Z i)
    (r₁ : ∀ i j, P i j ⟶ Z j) (hp : ∀ i, p i ≫ a = aZ i)
    (h₀ : ∀ i j, r₀ i j ≫ aZ i = aP i j) (h₁ : ∀ i j, r₁ i j ≫ aZ j = aP i j),
    IsFpqcCovering B S hS (fun i ↦ (p i).hom) →
    (∀ i j, IsPullback (r₀ i j) (r₁ i j) (p i) (p j)) →
    ∀ (F : Modules.{u, u} B S hS X.1 X.2)
      (K : ∀ i, Subobject ((modulePullback B S hS (aZ i)).obj F)),
      (∀ i, (cokernel (K i).arrow).IsQuasicoherentOnSite) →
      (∀ i j, quotientRestrictOver (r₀ i j) (h₀ i j) F (K i) =
        quotientRestrictOver (r₁ i j) (h₁ i j) F (K j)) →
      ∃ K₀ : Subobject ((modulePullback B S hS a).obj F),
        (cokernel K₀.arrow).IsQuasicoherentOnSite ∧
          ∀ i, quotientRestrictOver (p i) (hp i) F K₀ = K i

/-! ### Quasi-coherence of the quotients produced by the two constructions -/

/-- The quotient by a transported subobject is the original quotient, so it is quasi-coherent as
soon as that one is. -/
theorem isQuasicoherentOnSite_cokernel_quotientTransport {W : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS W.1 W.2} (ι : N ≅ M) {K : Subobject M}
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    (cokernel (quotientTransport ι K).arrow).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (quotientTransportCokernelIso ι K).symm hK

/-- The quotient by a restricted subobject is an inverse image of the original quotient, so it is
quasi-coherent as soon as that one is; this consumes Stacks 03GA. -/
theorem isQuasicoherentOnSite_cokernel_quotientRestrictOver
    (hqc : PullbackPreservesQuasicoherenceEverywhere B S hS)
    {X W W' : AlgebraicSpaces B S hS} {a : W ⟶ X} {a' : W' ⟶ X} (g : W' ⟶ W) (h : g ≫ a = a')
    (F : Modules.{u, u} B S hS X.1 X.2) {K : Subobject ((modulePullback B S hS a).obj F)}
    (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    (cokernel (quotientRestrictOver g h F K).arrow).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (quotientRestrictOverCokernelIso g h F K).symm
    (isQuasicoherentOnSite_modulePullback B S hS g (hqc g) _ hK)

end RestrictOver

export AlgebraicGeometry.Space.RestrictOver (DescendsQuotientsAlongFpqcCovering
  FinitePresentationOnSiteDescendsAlongFpqcCovering
  FlatOverDescendsAlongFpqcCovering
  FlatOverPullbackOver KernelQuasicoherent
  PullbackPreservesQuasicoherenceEverywhere
  baseChangeAlong baseChangeAlong_comp
  baseChangeAlong_comp_inclusion
  baseChangeAlong_comp_projection
  eq_of_quotientRestrictOver_eq
  isFpqcCovering_baseChangeAlong
  isPullback_baseChangeAlong
  isPullback_baseChangeAlong_pair
  isQuasicoherentOnSite_cokernel_quotientRestrictOver
  isQuasicoherentOnSite_cokernel_quotientTransport
  quotientRestrictOver quotientRestrictOverCokernelIso
  quotientRestrictOver_comp
  quotientRestrictOver_eq_quotientTransport)

end AlgebraicGeometry.Space

end
