module

public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.FirstVariable
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.CanTwistCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackDictionary
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningPullback
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# The dual `(p^*M)^∨` of the pullback of a module to the blowup

Let `p : X → Spec(A)` be the blowup of `Spec(A)` in `I`, `Yₙ ⊆ X` the `n`-th thickening of the
exceptional divisor and `M` an `A/Iⁿ`-module. The duality step of [Stacks, Tag 0GAC] and the
dotted-arrow argument of [Stacks, Tag 0GAD] use the dual

`(p^*M)^∨ = SheafHom_{𝒪_X}(p^*M, 𝒪_{Yₙ})`

of [Stacks, Tag 0GAB], its twists `(p^*M)^∨(q) = (p^*M)^∨ ⊗ 𝒪_X(q)`, and the maps
`D_u = (p^*u)^∨ : (p^*M')^∨ → (p^*M)^∨` it attaches to `u : M → M'`. This file builds them, once,
as a genuine sheaf construction: the internal Hom `Stacks.Algebraization.sheafHomFunctor` of the
blowup, out of `p^*M = p^*(M~)` (`blowupPullback` of the underlying `A`-module), into the
structure sheaf `𝒪_{Yₙ}` of the thickening, contravariant in `M` by precomposition.

Homomorphisms of `𝒪_X`-modules `p^*M → 𝒪_{Yₙ}` and `A`-linear maps into `Γ(X, 𝒪_{Yₙ})` are both
read off the global sections of the dual (`blowupDualSectionsEquiv`): the global sections of an
internal Hom are the morphisms (`Stacks.Algebraization.internalHomSectionsTopEquiv`) and
`p^* ⊣ Γ(X, -)` (`blowupPullbackAdjunction`).

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupModPullback`: `M ↦ p^*(M~)` for `A/Iⁿ`-modules.
* `Stacks.LocalCohomology.UniformityIII.blowupDual`: `(p^*M)^∨ = SheafHom(p^*M, 𝒪_{Yₙ})`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualMap`: `(p^*u)^∨`, and
  `blowupDualFunctor`, the dual as a functor `(Mod(A/Iⁿ))ᵒᵖ ⥤ Mod(𝒪_X)`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualTwist`: the twist `(p^*M)^∨(t)`, and the
  twisting maps `blowupDualTwistLE`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualSectionsEquiv`: global sections of the dual
  are homomorphisms `p^*M ⟶ 𝒪_{Yₙ}`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.isQuasicoherent_blowupDual`: for `M` finitely presented
  the dual and its twists are quasi-coherent ([Stacks, Tag 01LA]).
* `Stacks.LocalCohomology.UniformityIII.blowupDualSectionsEquiv_map`: the dictionary is natural
  in `M`.

## References

* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ)

/-! ### The pullback and its dual -/

/-- **`M ↦ p^*M`** for `A/Iⁿ`-modules: the pullback to the blowup of `M~`, where `M` is read as an
`A`-module along `A → A/Iⁿ`. -/
abbrev blowupModPullback : ModuleCat.{u} (A ⧸ I ^ n) ⥤ (blowupScheme I).Modules :=
  ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)) ⋙ blowupPullback I

/-- `p^*M` is `blowupPullback` of the underlying `A`-module. -/
theorem blowupModPullback_obj (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    (blowupModPullback I n).obj N = (blowupPullback I).obj (resModule I n N) :=
  rfl

/-- **The dual `(p^*M)^∨ = SheafHom_{𝒪_X}(p^*M, 𝒪_{Yₙ})`** of [Stacks, Tag 0GAB], on the blowup. -/
abbrev blowupDual (N : ModuleCat.{u} (A ⧸ I ^ n)) : (blowupScheme I).Modules :=
  (Stacks.Algebraization.sheafHomFunctor (blowupScheme I) ((blowupModPullback I n).obj N)).obj
    (thickeningSheaf I n)

/-- **`D_u = (p^*u)^∨ : (p^*M')^∨ ⟶ (p^*M)^∨`**, precomposition with `p^*u`. -/
def blowupDualMap {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N') :
    blowupDual I n N' ⟶ blowupDual I n N :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft (blowupScheme I).sheaf.obj
    ((blowupModPullback I n).map f).val⟩

/-- `(p^*𝟙)^∨ = 𝟙`. -/
theorem blowupDualMap_id (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    blowupDualMap I n (𝟙 N) = 𝟙 _ := by
  unfold blowupDualMap
  rw [(blowupModPullback I n).map_id]
  ext
  rfl

/-- `(p^*(f ≫ g))^∨ = (p^*g)^∨ ≫ (p^*f)^∨`. -/
theorem blowupDualMap_comp {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N') (g : N' ⟶ N'') :
    blowupDualMap I n (f ≫ g) = blowupDualMap I n g ≫ blowupDualMap I n f := by
  unfold blowupDualMap
  rw [(blowupModPullback I n).map_comp]
  ext
  rfl

/-- **The dual as a functor** `(Mod(A/Iⁿ))ᵒᵖ ⥤ Mod(𝒪_X)`, `M ↦ (p^*M)^∨`. -/
def blowupDualFunctor : (ModuleCat.{u} (A ⧸ I ^ n))ᵒᵖ ⥤ (blowupScheme I).Modules where
  obj N := blowupDual I n N.unop
  map f := blowupDualMap I n f.unop
  map_id N := blowupDualMap_id I n N.unop
  map_comp f g := blowupDualMap_comp I n g.unop f.unop

/-- The twist `(p^*M)^∨(t) = (p^*M)^∨ ⊗ 𝒪_X(t)`, `t ∈ ℤ`. -/
abbrev blowupDualTwist (N : ModuleCat.{u} (A ⧸ I ^ n)) (t : ℤ) : (blowupScheme I).Modules :=
  blowupDual I n N ⊗ blowupTwistInt I t

/-- The twisting map `(p^*M)^∨(t) ⟶ (p^*M)^∨(t')` for `t' ≤ t`. -/
abbrev blowupDualTwistLE (N : ModuleCat.{u} (A ⧸ I ^ n)) {t t' : ℤ} (h : t' ≤ t) :
    blowupDualTwist I n N t ⟶ blowupDualTwist I n N t' :=
  blowupDual I n N ◁ blowupTwistLE I h

/-- The twisting maps compose. -/
theorem blowupDualTwistLE_trans (N : ModuleCat.{u} (A ⧸ I ^ n)) {t t' t'' : ℤ} (h : t' ≤ t)
    (h' : t'' ≤ t') :
    blowupDualTwistLE I n N h ≫ blowupDualTwistLE I n N h' =
      blowupDualTwistLE I n N (h'.trans h) := by
  rw [← MonoidalCategory.whiskerLeft_comp, blowupTwistLE_trans]

/-- `D_u` commutes with the twisting maps. -/
theorem blowupDualMap_twist_comm {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N') {t t' : ℤ}
    (h : t' ≤ t) :
    blowupDualMap I n f ▷ blowupTwistInt I t ≫ blowupDualTwistLE I n N h =
      blowupDualTwistLE I n N' h ≫ blowupDualMap I n f ▷ blowupTwistInt I t' :=
  (whisker_exchange _ _).symm

/-! ### Quasi-coherence -/

/-- **`p^*M` is of finite presentation** for `M` finitely presented over `A`: `M~` is
([Stacks, Tag 01PC]) and pullback preserves finite presentation ([Stacks, Tag 01BQ]). -/
theorem isFinitePresentation_blowupModPullback (N : ModuleCat.{u} (A ⧸ I ^ n))
    [Module.FinitePresentation A (resModule I n N)] :
    ((blowupModPullback I n).obj N).IsFinitePresentation :=
  Stacks.Modules.isFinitePresentation_pullback (Stacks.Blowup.toSpec I) _
    ((tilde_isFinitePresentation_iff (R := CommRingCat.of A) (resModule I n N)).2 inferInstance)

/-- **The dual is quasi-coherent** for `M` finitely presented over `A` ([Stacks, Tag 01LA]): the
internal Hom from a module of finite presentation into the quasi-coherent `𝒪_{Yₙ}`. -/
theorem isQuasicoherent_blowupDual (N : ModuleCat.{u} (A ⧸ I ^ n))
    [Module.FinitePresentation A (resModule I n N)] : (blowupDual I n N).IsQuasicoherent := by
  have := isFinitePresentation_blowupModPullback I n N
  exact sheafHom_isQuasicoherent _ _

/-- The twists of the dual are quasi-coherent, for `M` finitely presented over `A`. -/
theorem isQuasicoherent_blowupDualTwist (N : ModuleCat.{u} (A ⧸ I ^ n))
    [Module.FinitePresentation A (resModule I n N)] (t : ℤ) :
    (blowupDualTwist I n N t).IsQuasicoherent := by
  have := isQuasicoherent_blowupDual I n N
  infer_instance

/-! ### Global sections of the dual -/

/-- **Global sections of `(p^*M)^∨` are the homomorphisms `p^*M ⟶ 𝒪_{Yₙ}`**
(`Stacks.Algebraization.internalHomSectionsTopEquiv`). -/
def blowupDualSectionsEquiv (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    (blowupΓmod I).obj (blowupDual I n N) ≃+
      ((blowupModPullback I n).obj N ⟶ thickeningSheaf I n) :=
  Stacks.Algebraization.internalHomSectionsTopEquiv _ _

/-- The section of `(p^*M)^∨` attached to a homomorphism `p^*M ⟶ 𝒪_{Yₙ}`. -/
def blowupDualSection {N : ModuleCat.{u} (A ⧸ I ^ n)}
    (φ : (blowupModPullback I n).obj N ⟶ thickeningSheaf I n) :
    (blowupΓmod I).obj (blowupDual I n N) :=
  (blowupDualSectionsEquiv I n N).symm φ

/-- **The dictionary is natural in `M`**: `D_u` acts on global sections by precomposition with
`p^*u`. -/
theorem blowupDualSectionsEquiv_map {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (φ : (blowupModPullback I n).obj N' ⟶ thickeningSheaf I n) :
    blowupDualSectionsEquiv I n N ((blowupΓmod I).map (blowupDualMap I n f)
        (blowupDualSection I n φ)) =
      (blowupModPullback I n).map f ≫ φ := by
  rw [blowupDualSectionsEquiv, Stacks.Algebraization.internalHomSectionsTopEquiv]
  refine (AddEquiv.symm_apply_eq _).2 ?_
  exact ((Stacks.Algebraization.topOverForget (blowupScheme I)).map_comp _ _).symm

end Stacks.LocalCohomology.UniformityIII

end
