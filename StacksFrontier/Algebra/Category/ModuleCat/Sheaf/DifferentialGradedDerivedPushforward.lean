module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardHom

/-!
# Derived internal hom and derived pushforward of sheaves of differential graded modules

Let `(C, O)` be a ringed site and let `(A, d)` be a sheaf of differential graded `O`-algebras.
Every right differential graded `A`-module admits a quasi-isomorphism into a graded injective and
K-injective one, and a quasi-isomorphism between two such modules is already an isomorphism of
the homotopy category; so an exact functor out of `K(Mod(A, d))` has a right derived extension
`D(A, d) ⟶ D` whose value on a graded injective and K-injective module `I` is the value of the
functor at `I`. Two instances of this are named here.

* For differential graded `O`-algebras `A`, `B` and a differential graded `(A, B)`-bimodule `N`,
  the right derived extension `RHom_B(N, -) : D(B, d) ⟶ D(A, d)` of the internal hom functor
  `SheafHom^dg_B(N, -)` is the *derived internal hom*.
* For a morphism of ringed sites `f`, a differential graded `O_C`-algebra `A`, a differential
  graded `O_D`-algebra `B` and a homomorphism `φ : B ⟶ f_*A`, the right derived extension
  `Rf_* : D(A, d) ⟶ D(B, d)` of the direct image `f_*` is the *derived pushforward*.

Both are read here as the property of a functor of derived categories that it is such a right
derived extension, which determines it up to isomorphism at every object of the source. That the
two extensions exist is Tag 0FTP,
`SheafOfModules.DifferentialGradedModule.exists_derivedInternalHom_and_derivedPushforward`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.IsDGInjective` is the conjunction of graded
  injectivity and K-injectivity, the property of a right differential graded module which makes
  it compute right derived functors.
* `SheafOfModules.DifferentialGradedModule.ComputesOnDGInjective` says that a functor of derived
  categories takes, on the image of a graded injective and K-injective module, the value
  prescribed by a given functor of differential graded modules, compatibly with homomorphisms of
  such modules; this is what it means for the functor to be the right derived extension computed
  by graded injective and K-injective modules.
* `SheafOfModules.DifferentialGradedModule.IsDerivedInternalHom` says that a functor
  `D(B, d) ⟶ D(A, d)` is the derived internal hom `RHom_B(N, -)`, and
  `SheafOfModules.DifferentialGradedModule.IsDerivedPushforward` says that a functor
  `D(A, d) ⟶ D(B, d)` is the derived pushforward `Rf_*`.
* `SheafOfModules.DifferentialGradedModule.pushforwardData` is the constructed direct image read
  through its universal property: the counit off `f_*M` which is the identity on local sections
  exhibits `f_*M` as the direct image of `M`.

## Main results

* `SheafOfModules.DifferentialGradedModule.nonempty_obj_iso_of_computesOnDGInjective`: two right
  derived extensions of one functor, each computed by the graded injective and K-injective
  modules, take isomorphic values at every object of the derived category.
* `SheafOfModules.DifferentialGradedModule.nonempty_derivedInternalHom_obj_iso` and
  `...nonempty_derivedPushforward_obj_iso`: so the derived internal hom and the derived
  pushforward are each determined up to isomorphism at every object.
* `SheafOfModules.DifferentialGradedModule.commutator_smul_eq_of_isInternalHom_self` and
  `...commutator_smul_eq_of_sheafHomFunctorData`: an internal hom of a right differential graded
  module with itself makes every commutator of the sheaf of rings annihilate that module.

## Implementation notes

The derived categories are `SheafOfModules.DifferentialGradedModule.derivedCategory`, the
localization of the homotopy category of right differential graded modules at the
quasi-isomorphisms, with localization functor
`SheafOfModules.DifferentialGradedModule.toDerivedCategory` (Tag 0FT5), and the direct image is
`SheafOfModules.DifferentialGradedModule.pushforwardFunctor`. The section universe is preserved by
the direct image, because the sections of `f_*M` over `V` are the sections of `M` over `u V`.

The statements are over an arbitrary sheaf of rings on an arbitrary site, with independent
universes. The existence of graded injective and K-injective resolutions (Tag 0FT0) is the
hypothesis `hres`; over a ringed site whose site, morphism and ring universes agree it is
`SheafOfModules.DifferentialGradedModule.hasKInjectiveResolutions_dg`.

A quasi-isomorphism of right differential graded modules is a homomorphism which is a
quasi-isomorphism on the underlying complexes. `ComputesOnDGInjective` prescribes a functor of
derived categories only on the images of the graded injective and K-injective modules, so two
right derived extensions of one functor agree up to isomorphism at every object, not as functors.

## References

* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
* [Stacks Project, Tag 0FSP](https://stacks.math.columbia.edu/tag/0FSP)
* [Stacks Project, Tag 0FSU](https://stacks.math.columbia.edu/tag/0FSU)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t t' a a' m m' s z v u v' u' d e d' e'

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### Differential graded injective modules, and the derived category -/

section DGInjective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A right differential graded module is *differential graded injective* when it is both graded
injective and K-injective. These are the modules whose images in the derived category compute
right derived functors. -/
abbrev IsDGInjective {A : DifferentialGradedAlgebra.{t, a} R}
    (I : DifferentialGradedModule.{t, a, m} A) : Prop :=
  GradedInjective I ∧ IsKInjective I

/-- The identity of `M`, as a degree-zero local homomorphism of right differential graded
`A`-modules. -/
private def idLocalHom {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (U : C) : LocalHom M M 0 U where
  app i j hij V := by
    obtain rfl : i = j := by lia
    exact AddMonoidHom.id _
  map_smul i j hij V r x := by
    obtain rfl : i = j := by lia
    rfl
  naturality i j hij V W g x := by
    obtain rfl : i = j := by lia
    rfl
  isLinear i j hij p V x b := by
    obtain rfl : i = j := by lia
    rfl

/-- **The internal hom of a module with itself forces the sheaf of rings to act commutatively on
it.** If a complex `H` is the internal hom `SheafHom^dg_A(M, M)`, then for every pair of local
sections `r`, `b` of the sheaf of rings their commutator annihilates every local section of `M`.
-/
theorem commutator_smul_eq_of_isInternalHom_self {A : DifferentialGradedAlgebra.{t, a} R}
    {M : DifferentialGradedModule.{t, a, m} A}
    {H : CochainComplex (SheafOfModules.{s} R) ℤ} (h : IsInternalHom M M H)
    (U : C) (r : R.obj.obj (Opposite.op U)) (i : ℤ) (V : Over U)
    (b : R.obj.obj (Opposite.op V.left))
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (R.obj.map V.hom.op r * b) • x = (b * R.obj.map V.hom.op r) • x := by
  set p := (h.sectionsEquiv 0 U).symm (idLocalHom M U) with hp
  have hid : h.sectionsEquiv 0 U p = idLocalHom M U := by rw [hp, Equiv.apply_symm_apply]
  have h₁ := (h.sectionsEquiv 0 U p).map_smul i i (by lia) V b x
  have h₂ := (h.sectionsEquiv 0 U (r • p)).map_smul i i (by lia) V b x
  have e₁ := h.sectionsEquiv_smul 0 U r p i i (by lia) V x
  have e₂ := h.sectionsEquiv_smul 0 U r p i i (by lia) V (b • x)
  rw [h₁] at e₂
  rwa [e₂, e₁, smul_smul, smul_smul, hid] at h₂

/-- **An internal hom functor for a bimodule forces the sheaf of rings to act on the bimodule
through its abelianization.** A term of `SheafOfModules.SheafHomFunctorData` provides, at the
bimodule `N` read as a right differential graded `A'`-module, an internal hom of `N` with itself;
so by `SheafOfModules.DifferentialGradedModule.commutator_smul_eq_of_isInternalHom_self` every
commutator `rb - br` of local sections of the sheaf of rings annihilates every local section
of `N`. -/
theorem commutator_smul_eq_of_sheafHomFunctorData {A A' : DifferentialGradedAlgebra.{t, a} R}
    {N : DifferentialGradedBimodule.{t, a, z} A A'} (S : SheafHomFunctorData.{t, a, m, z, z} N)
    (U : C) (r : R.obj.obj (Opposite.op U)) (i : ℤ) (V : Over U)
    (b : R.obj.obj (Opposite.op V.left))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (R.obj.map V.hom.op r * b) • x = (b * R.obj.map V.hom.op r) • x :=
  commutator_smul_eq_of_isInternalHom_self (M := N.toRightModule)
    (H := (S.functor.obj N.toRightModule).complex)
    (S.isSheafHom N.toRightModule).isInternalHom U r i V b x

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Every object of the derived category `D(A, d)` is isomorphic to the image of a right
differential graded module. -/
theorem exists_iso_toDerivedCategory (A : DifferentialGradedAlgebra.{t, a} R)
    (X : derivedCategory.{t, a, m} A) :
    ∃ M : DifferentialGradedModule.{t, a, m} A,
      Nonempty ((toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj M) ≅ X) :=
  ⟨X.as.obj.as, ⟨Iso.refl _⟩⟩

/-- A homomorphism of right differential graded modules which is a quasi-isomorphism on the
underlying complexes becomes an isomorphism of the derived category. -/
theorem isIso_toDerivedCategory_map_of_quasiIso {A : DifferentialGradedAlgebra.{t, a} R}
    {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N)
    (hf : QuasiIso f.toHomologicalComplex) :
    IsIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map f)) :=
  Localization.inverts (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A) _
    ((quasiIsomorphisms_quotient_map_iff f).2 hf)

end DGInjective

/-! ### The right derived extension -/

section ComputesOnDGInjective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]

/-- A functor `L : D(A, d) ⥤ D(A', d)` of derived categories is *computed on graded injective and
K-injective modules* by a functor `F` of differential graded modules when `L` takes the image of a
graded injective and K-injective module `I` to the image of `F I`, and takes the image of a
homomorphism of such modules to the image of its value under `F`: `L` is the right derived
extension of `F`. -/
structure ComputesOnDGInjective {A : DifferentialGradedAlgebra.{t, a} R}
    {A' : DifferentialGradedAlgebra.{t', a'} R'}
    (F : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t', a', m'} A')
    (L : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t', a', m'} A') where
  /-- On the image in the derived category of a graded injective and K-injective module `I`, the
  functor takes the value prescribed by `F`. -/
  obj_eq {I : DifferentialGradedModule.{t, a, m} A} (hI : IsDGInjective I) :
    L.obj ((toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj I)) =
      (toDerivedCategory.{t', a', m'} A').obj ((HomotopyCategory.quotient A').obj (F.obj I))
  /-- On the image of a homomorphism of graded injective and K-injective modules, the functor is
  the image of its value under `F`, read through the identifications of the previous clause. -/
  map_eq {I I' : DifferentialGradedModule.{t, a, m} A} (hI : IsDGInjective I)
      (hI' : IsDGInjective I') (ψ : I ⟶ I') :
    L.map ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map ψ)) =
      eqToHom (obj_eq hI) ≫
        (toDerivedCategory.{t', a', m'} A').map
            ((HomotopyCategory.quotient A').map (F.map ψ)) ≫
          eqToHom (obj_eq hI').symm

variable {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t', a'} R'}
  {F : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t', a', m'} A'}

/-- Two right derived extensions of one functor of differential graded modules, each computed by
the graded injective and K-injective modules, take isomorphic values at every object of the
derived category, provided every module admits a quasi-isomorphism into a graded injective and
K-injective one (`hres`). -/
theorem nonempty_obj_iso_of_computesOnDGInjective
    (hres : ∀ M : DifferentialGradedModule.{t, a, m} A,
      ∃ (I : DifferentialGradedModule.{t, a, m} A) (i : M ⟶ I),
        IsDGInjective I ∧ QuasiIso i.toHomologicalComplex)
    {L L' : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t', a', m'} A'}
    (h : ComputesOnDGInjective F L) (h' : ComputesOnDGInjective F L')
    (X : derivedCategory.{t, a, m} A) :
    Nonempty (L.obj X ≅ L'.obj X) := by
  obtain ⟨M, ⟨eM⟩⟩ := exists_iso_toDerivedCategory A X
  obtain ⟨I, i, hI, hi⟩ := hres M
  have := isIso_toDerivedCategory_map_of_quasiIso i hi
  let e : (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj I) ≅ X :=
    (asIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map i))).symm ≪≫ eM
  exact ⟨(L.mapIso e).symm ≪≫ eqToIso ((h.obj_eq hI).trans (h'.obj_eq hI).symm) ≪≫
    L'.mapIso e⟩

end ComputesOnDGInjective

/-! ### Derived internal hom -/

section DerivedInternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A A'}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]

/-- A functor `L : D(A', d) ⥤ D(A, d)` between the derived categories *is the derived internal
hom* `RHom_{A'}(N, -)` of a differential graded `(A, A')`-bimodule `N` when it is the right
derived extension of the internal hom functor `SheafHom^dg_{A'}(N, -)`, that is when its value on
the image of a graded injective and K-injective right differential graded `A'`-module `I` is the
image of `SheafHom^dg_{A'}(N, I)`. -/
def IsDerivedInternalHom (S : SheafHomFunctorData.{t, a, m, s, z} N)
    (L : derivedCategory.{t, a, s} A' ⥤ derivedCategory.{t, a, m} A) : Prop :=
  ComputesOnDGInjective S.functor L

/-- The derived internal hom is determined up to isomorphism at every object of `D(A', d)`,
granted the resolution theorem for `A'`. -/
theorem nonempty_derivedInternalHom_obj_iso
    (hres : ∀ M : DifferentialGradedModule.{t, a, s} A',
      ∃ (I : DifferentialGradedModule.{t, a, s} A') (i : M ⟶ I),
        IsDGInjective I ∧ QuasiIso i.toHomologicalComplex)
    {S : SheafHomFunctorData.{t, a, m, s, z} N}
    {L L' : derivedCategory.{t, a, s} A' ⥤ derivedCategory.{t, a, m} A}
    (h : IsDerivedInternalHom S L) (h' : IsDerivedInternalHom S L')
    (X : derivedCategory.{t, a, s} A') :
    Nonempty (L.obj X ≅ L'.obj X) :=
  nonempty_obj_iso_of_computesOnDGInjective hres h h' X

end DerivedInternalHom

/-! ### Derived pushforward -/

section DerivedPushforward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}

/-- **The direct image is a `SheafOfModules.DifferentialGradedModule.PushforwardData`.** The
constructed direct image `SheafOfModules.DifferentialGradedModule.pushforwardObj`, together with
the `φ`-semilinear map off it which is the identity on local sections, satisfies the universal
property `SheafOfModules.DifferentialGradedModule.IsPushforward`: a `φ`-semilinear map into `M` is
the same thing as a morphism into `f_*M`, by
`SheafOfModules.DifferentialGradedModule.semilinearHomEquiv`, and the factorisation through the
counit is that bijection. -/
noncomputable def pushforwardData (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A) :
    PushforwardData.{t, a, a', m, m} φ where
  obj M := pushforwardObj φ M
  counit M := (semilinearHomEquiv φ (pushforwardObj φ M) M).symm (𝟙 _)
  isPushforward M :=
    { lift := fun θ' => semilinearHomEquiv φ _ M θ'
      fac := fun _ => SemilinearHom.ext fun _ _ _ => rfl
      uniq := fun θ' h hh => (semilinearHomEquiv φ _ M).symm_apply_eq.1 <| by
        rw [← hh]
        exact SemilinearHom.ext fun _ _ _ => rfl }

/-- A functor `L : D(A, d) ⥤ D(B, d)` between the derived categories *is the derived pushforward*
`Rf_*` along a morphism of ringed sites `f` and a homomorphism `φ : B ⟶ f_*A` when it is the right
derived extension of the direct image `f_*`, that is when its value on the image of a graded
injective and K-injective right differential graded `A`-module `I` is the image of `f_*I`. -/
def IsDerivedPushforward [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J' AddCommGrpCat.{m}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (L : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a', m} B) : Prop :=
  ComputesOnDGInjective (pushforwardFunctor.{t, a, m} φ) L

/-- The derived pushforward is determined up to isomorphism at every object of `D(A, d)`, granted
the resolution theorem for `A`. -/
theorem nonempty_derivedPushforward_obj_iso [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J' AddCommGrpCat.{m}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (hres : ∀ M : DifferentialGradedModule.{t, a, m} A,
      ∃ (I : DifferentialGradedModule.{t, a, m} A) (i : M ⟶ I),
        IsDGInjective I ∧ QuasiIso i.toHomologicalComplex)
    {L L' : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a', m} B}
    (h : IsDerivedPushforward (φ := φ) L) (h' : IsDerivedPushforward (φ := φ) L')
    (X : derivedCategory.{t, a, m} A) :
    Nonempty (L.obj X ≅ L'.obj X) :=
  nonempty_obj_iso_of_computesOnDGInjective hres h h' X

end DerivedPushforward

end DifferentialGradedModule

end SheafOfModules

end
