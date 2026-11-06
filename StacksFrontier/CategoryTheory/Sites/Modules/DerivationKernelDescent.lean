module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass

/-!
# Derivation descent along a locally surjective homomorphism of sheaves of rings

Let `φ : 𝒜 ⟶ 𝒬` be a locally surjective homomorphism of sheaves of commutative rings on a site
`(C, J)`, let `a : ℛ ⟶ 𝒜` be a homomorphism from a presheaf of commutative rings, and let `M` be
a sheaf of `𝒬`-modules.  This file identifies the `ℛ`-derivations of `𝒬` with values in `M` with
those `ℛ`-derivations of `𝒜` with values in `M` — scalars restricted along `φ` — which annihilate
the kernel of `φ`.

## Main definitions

* `Stacks.Sites.Conormal.restrictDerivation`: an `ℛ`-derivation of `𝒬` restricted along `φ`, as
  an `ℛ`-derivation of `𝒜`.  It annihilates the kernel of `φ` by
  `Stacks.Sites.Conormal.restrictDerivation_eq_zero_of_mem_kernel`.
* `Stacks.Sites.Conormal.quotientDerivationOfVanishing`: an `ℛ`-derivation of `𝒜` annihilating
  the kernel of `φ`, read as an `ℛ`-derivation of the image presheaf `𝒜/ker φ`.  This is the
  objectwise quotient step, and it is the one place where the vanishing hypothesis is used.

## Main results

* `Stacks.Sites.Conormal.derivation_ext_of_isLocallySurjective`: two derivations of `𝒬` agreeing
  on the sections coming from `𝒜` are equal, because those sections cover.
* `Stacks.Sites.Conormal.existsUnique_derivation_of_vanishing_on_kernel`: an `ℛ`-derivation of
  `𝒜` with values in `M` annihilating `ker φ` is the restriction along `φ` of a unique
  `ℛ`-derivation of `𝒬`.
* `Stacks.Sites.Conormal.derivationKernelEquiv`: the two descriptions as a bijection.

## Implementation notes

**The universe of the module sections is free, and that is the point of this file.**
`Stacks.Sites.Conormal.quotientDerivationEquiv` of
`StacksFrontier/CategoryTheory/Sites/Modules/CorepresentingConormalSequence.lean` is the same descent
at the objectwise quotient `𝒜/ker φ`, but it is stated for a coefficient module whose sections
live at `max w u v z`, the maximum of the universes of the site's objects, its arrows, its rings
and a small model.  On a site whose objects live one universe above its arrows and its rings —
the small étale site of an algebraic space is such a site — that maximum is strictly above the
universe of the structure rings, so that statement does not apply to a sheaf of modules whose
sections live at the universe of the rings.  Here the only coefficient-universe constraint is
the one carried by the gluing step, namely that it agrees with the universe of the sheaves of
rings, which is what a sheaf of `𝒪`-modules on a ringed site satisfies.

The descent is obtained in two steps rather than one, because the gluing step
`Stacks.SheafOfModules.exists_derivation_of_locallyBijective` asks for a locally *bijective*
homomorphism: the derivation is first pushed down to the objectwise quotient
`Stacks.Sites.Conormal.quotientPresheaf`, along which the comparison
`Stacks.Sites.Conormal.quotientToTarget` to `𝒬` is injective on every object and locally
surjective, hence locally bijective.  The quotient step is `QuotientAddGroup.lift`: a derivation
is additive but not linear, so the universal property of the quotient *module* does not apply and
the universal property of the quotient *additive group* is what lifts it.

## References

* [Stacks Project, Tag 08TF](https://stacks.math.columbia.edu/tag/08TF), the conormal sequence of
  a surjection of sheaves of rings, whose exactness at the middle term this descent is the
  derivation-level content of.
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} {A Q : Sheaf J CommRingCat.{w}}
  (a : R ⟶ A.obj) (φ : A ⟶ Q)
  (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))

/-- The restriction of scalars of a sheaf of `𝒬`-modules along a homomorphism of presheaves of
commutative rings with target the presheaf underlying `𝒬`. -/
noncomputable abbrev restrictModuleAlong {P : Cᵒᵖ ⥤ CommRingCat.{w}} (ψ : P ⟶ Q.obj) :
    PresheafOfModules.{w} (P ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight ψ (forget₂ CommRingCat.{w} RingCat.{w}))).obj M.val

/-- **An `ℛ`-derivation of `𝒬` read as an `ℛ`-derivation of `𝒜`.**  Precomposition with `φ` on
sections; additivity, the Leibniz rule and compatibility with restriction are inherited, and the
scalar action is the same because `𝒜` acts on `M` through `φ`. -/
noncomputable def restrictDerivation (D : PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ φ.hom)) :
    PresheafOfModulesOfCommRing.Derivation' (restrictModuleAlong J M φ.hom) a where
  d {X} := (D.d (X := X)).comp (φ.hom.app X).hom.toAddMonoidHom
  d_mul {X} x y := by
    change D.d ((φ.hom.app X) (x * y)) = _
    rw [map_mul, D.d_mul]
    rfl
  d_map {X Y} f x := by
    change D.d ((φ.hom.app Y) (A.obj.map f x)) = _
    rw [φ.hom.naturality_apply f x]
    exact D.d_map f _
  d_app {X} x := by
    change D.d ((φ.hom.app X) ((a.app X) x)) = 0
    exact D.d_app x

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Stacks.Sites.Conormal.restrictDerivation` is precomposition with `φ` on sections. -/
lemma restrictDerivation_d (D : PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ φ.hom)) (X : Cᵒᵖ) (x : A.obj.obj X) :
    (restrictDerivation J a φ M D).d x = D.d ((φ.hom.app X) x) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The restriction along `φ` of a derivation of `𝒬` annihilates the kernel of `φ`. -/
lemma restrictDerivation_eq_zero_of_mem_kernel (D : PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ φ.hom)) (X : Cᵒᵖ)
    (x : A.obj.obj X) (hx : (φ.hom.app X) x = 0) :
    (restrictDerivation J a φ M D).d x = 0 :=
  (restrictDerivation_d J a φ M D X x).trans ((congrArg D.d hx).trans (map_zero D.d))

/-- **A derivation of `𝒜` annihilating the kernel of `φ`, read on the image presheaf.**  A
derivation is additive but not linear, so the lift through the objectwise quotient
`𝒜/ker φ` is the universal property of a quotient of additive groups. -/
noncomputable def quotientDerivationOfVanishing
    (D : PresheafOfModulesOfCommRing.Derivation' (restrictModuleAlong J M φ.hom) a)
    (hD : ∀ (X : Cᵒᵖ) (x : A.obj.obj X), (φ.hom.app X) x = 0 → D.d x = 0) :
    PresheafOfModulesOfCommRing.Derivation' (restrictModuleAlong J M (quotientToTarget φ.hom)) (a ≫ toQuotient φ.hom) where
  d {X} := QuotientAddGroup.lift (kernelIdeal φ.hom X).toAddSubgroup D.d
    fun x hx ↦ hD X x (RingHom.mem_ker.1 hx)
  d_mul {X} x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change D.d (x * y) = _
    rw [D.d_mul]
    rfl
  d_map {X Y} f x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change D.d (A.obj.map f x) = _
    exact D.d_map f x
  d_app {X} x := D.d_app x

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The lift of a derivation to the image presheaf agrees with it on the classes of sections of
`𝒜`.  This is the defining equation of `Stacks.Sites.Conormal.quotientDerivationOfVanishing`. -/
lemma quotientDerivationOfVanishing_mk (D : PresheafOfModulesOfCommRing.Derivation' (restrictModuleAlong J M φ.hom) a)
    (hD : ∀ (X : Cᵒᵖ) (x : A.obj.obj X), (φ.hom.app X) x = 0 → D.d x = 0)
    (X : Cᵒᵖ) (x : A.obj.obj X) :
    (quotientDerivationOfVanishing J a φ M D hD).d ((toQuotient φ.hom).app X x) = D.d x :=
  rfl

variable [Presheaf.IsLocallySurjective J φ.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Two derivations of `𝒬` agreeing on the sections coming from `𝒜` are equal**, because `φ`
is locally surjective and the coefficient sheaf is separated. -/
theorem derivation_ext_of_isLocallySurjective (D E : PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ φ.hom))
    (h : ∀ (X : Cᵒᵖ) (x : A.obj.obj X),
      D.d ((φ.hom.app X) x) = E.d ((φ.hom.app X) x)) : D = E := by
  ext X x
  apply M.isSheaf.isSeparated X.unop _ (Presheaf.imageSieve_mem J φ.hom x)
  intro Y k hk
  obtain ⟨b, hb⟩ := hk
  change (M.val.map k.op).hom (D.d x) = (M.val.map k.op).hom (E.d x)
  have key : D.d (Q.obj.map k.op x) = E.d (Q.obj.map k.op x) := by
    rw [← hb]
    exact h _ _
  exact (D.d_map k.op x).symm.trans (key.trans (E.d_map k.op x))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Derivation descent along a locally surjective homomorphism of sheaves of rings.**  An
`ℛ`-derivation of `𝒜` with values in a sheaf of `𝒬`-modules which annihilates the kernel of
`φ : 𝒜 ⟶ 𝒬` is the restriction along `φ` of a unique `ℛ`-derivation of `𝒬`.

Existence is the gluing step
`Stacks.SheafOfModules.exists_derivation_of_locallyBijective` applied to
`Stacks.Sites.Conormal.quotientToTarget`, which is locally bijective; uniqueness is
`Stacks.Sites.Conormal.derivation_ext_of_isLocallySurjective`. -/
theorem existsUnique_derivation_of_vanishing_on_kernel
    (D : PresheafOfModulesOfCommRing.Derivation' (restrictModuleAlong J M φ.hom) a)
    (hD : ∀ (X : Cᵒᵖ) (x : A.obj.obj X), (φ.hom.app X) x = 0 → D.d x = 0) :
    ∃! D' : PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ φ.hom),
      ∀ (X : Cᵒᵖ) (x : A.obj.obj X), D'.d ((φ.hom.app X) x) = D.d x := by
  obtain ⟨D', hD'⟩ := Stacks.SheafOfModules.exists_derivation_extension_of_locallyBijective J
    (a ≫ toQuotient φ.hom) (quotientToTarget φ.hom) M
    (quotientDerivationOfVanishing J a φ M D hD)
  have h := fun (X : Cᵒᵖ) (x : A.obj.obj X) ↦ hD' X ((toQuotient φ.hom).app X x)
  exact ⟨D', h, fun E hE ↦ derivation_ext_of_isLocallySurjective J a φ M E D' fun X x ↦
    h X x ▸ hE X x⟩

/-- **The derivations of `𝒬` are the derivations of `𝒜` annihilating the kernel of `φ`.**  The
bijection is restriction along `φ`. -/
noncomputable def derivationKernelEquiv :
    PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ φ.hom) ≃
      {D : PresheafOfModulesOfCommRing.Derivation' (restrictModuleAlong J M φ.hom) a //
        ∀ (X : Cᵒᵖ) (x : A.obj.obj X), (φ.hom.app X) x = 0 → D.d x = 0} where
  toFun D := ⟨restrictDerivation J a φ M D,
    restrictDerivation_eq_zero_of_mem_kernel J a φ M D⟩
  invFun D := (existsUnique_derivation_of_vanishing_on_kernel J a φ M D.1 D.2).choose
  left_inv D := by
    refine derivation_ext_of_isLocallySurjective J a φ M _ D fun X x ↦ ?_
    exact (existsUnique_derivation_of_vanishing_on_kernel J a φ M _
      (restrictDerivation_eq_zero_of_mem_kernel J a φ M D)).choose_spec.1 X x
  right_inv D := by
    refine Subtype.ext ?_
    ext X x
    exact (existsUnique_derivation_of_vanishing_on_kernel J a φ M D.1 D.2).choose_spec.1 X x

end Stacks.Sites.Conormal

end
