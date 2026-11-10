module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealGradedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMapAmbientComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafPullbackMapEpi

/-!
# The canonical map of conormal algebras of a cartesian square of immersions

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `i` and `i'` immersions.  [Stacks Project, Tag 09RT] asserts that the canonical map

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`

of sheaves of graded `𝒪_Z`-algebras of [Stacks Project, Tag 09RS]
(`AlgebraicGeometry.Space.conormalAlgebraSquareMap`) is surjective, and that it is an isomorphism
if `g` is flat.  Both assertions are proved here.

## The proof

The canonical map of Stacks 09RS is built from the ambient homomorphism
`Ψ : g^*(⨁ Ker((f ≫ i')^♯)ⁿ) ⟶ ⨁ Ker(i^♯)ⁿ` induced by `g^♯`
(`AlgebraicGeometry.Space.kernelIdealGradedPullbackHom`), and in each degree it is the inverse
image along `i` of the *ambient comparison*
`χ : g^*(⨁ (𝓘')ⁿ) ⟶ ⨁ 𝓘ⁿ` (`AlgebraicGeometry.Space.conormalAlgebraSquareAmbientComparison`),
preceded by two isomorphisms
(`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison`).

* The degree-`n` component of `Ψ` is the transpose of pullback of regular functions
  (`AlgebraicGeometry.Space.modulePullbackHomFMap_kernelIdealGradedPullbackHom_app`), because the
  adjunction of sheaves of graded algebras of Stacks 0FQX is degreewise the adjunction of
  Stacks 03D7.  Hence `χ` is, in each degree `n ≥ 0`, induced by pullback of regular functions
  (`AlgebraicGeometry.Space.isInducedByPullback_conormalAlgebraSquareAmbientComparison_app`).
* For such a map `i^*χₙ` is an epimorphism, and for flat `g` an isomorphism, as soon as the
  square is cartesian and `i'` is an immersion: this is
  `AlgebraicGeometry.Space.epi_modulePullback_map_of_isPullback` and
  `AlgebraicGeometry.Space.isIso_modulePullback_map_of_isPullback_of_isFlat`, the étale-local
  reduction of the source to the scheme case, carried out on charts.
* In negative degrees both conormal algebras vanish.

## Main results

* `AlgebraicGeometry.Space.epi_conormalAlgebraSquareMap_app_of_isPullback`: **the surjectivity
  assertion of [Stacks Project, Tag 09RT]**: the canonical map is surjective in every degree.
* `AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMap_of_isPullback_of_isFlat`: **the flat
  assertion of [Stacks Project, Tag 09RT]**: if `g` is flat, the canonical map is an isomorphism
  of sheaves of graded algebras.

Only `i'` is required to be an immersion: in a cartesian square the base change `i` of an
immersion is one, so the statements specialise to the source's.

## References

* [Stacks Project, Tag 09RT](https://stacks.math.columbia.edu/tag/09RT)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 0635](https://stacks.math.columbia.edu/tag/0635)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- **A homomorphism of sheaves of graded algebras which is an isomorphism in every degree is an
isomorphism of sheaves of graded algebras**: the inverse family is multiplicative
(`SheafOfModules.GradedAlgebra.isoOfPieceIso`). -/
theorem isIso_of_forall_isIso_app {A D : GradedAlgebra.{t, a} R} (φ : A ⟶ D)
    (h : ∀ n, IsIso (φ.app n)) : IsIso φ := by
  let e := isoOfPieceIso (fun n => asIso (φ.app n)) φ.map_mul
  have he : e.hom = φ := Hom.ext fun n => rfl
  rw [← he]
  infer_instance

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' Z' : AlgebraicSpaces B S hS}

/-! ### The degreewise components of the ambient homomorphism -/

/-- The degree-`n` component of a transpose along the adjunction of sheaves of graded algebras
is the transpose along the adjunction of sheaves of modules of the degree-`n` component. -/
theorem kernelIdealGradedPullbackHom_app_eq (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (n : ℤ) :
    (kernelIdealGradedPullbackHom B S hS i g j hj).app n =
      ((smallEtaleRingedToposHom B S hS g).pullbackAdjPushforwardModulesViaComparison.homEquiv
        _ _).symm ((kernelIdealGradedPushforwardHom B S hS i g j hj).app n) := by
  refine Eq.trans (congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
    (Adjunction.homEquiv_counit _ _ _ _)) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_counit
    (smallEtaleRingedToposHom B S hS g).pullbackAdjPushforwardModulesViaComparison _ _ _).symm
  rfl

/-- Transposing along an adjunction transported along `e₁` and back along the one transported
along `e₁ ≪≫ e₂` is postcomposition with `e₂`. -/
private theorem homEquiv_ofNatIsoRight_trans_symm {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H K : D ⥤ C} (A : F ⊣ G) (e₁ : G ≅ H) (e₂ : H ≅ K) {P : C} {Q : D}
    (x : P ⟶ H.obj Q) :
    (A.ofNatIsoRight (e₁ ≪≫ e₂)).homEquiv P Q (((A.ofNatIsoRight e₁).homEquiv P Q).symm x) =
      x ≫ e₂.hom.app Q := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Equiv.apply_symm_apply]
  simp

/-- The two forms of the adjunction of Stacks 03D7 for the small étale ringed topoi differ by the
comparison of the two direct images of modules. -/
theorem modulePullbackAdjunction_homEquiv_viaComparison_symm
    {M : Modules.{u, u} B S hS X'.1 X'.2} {N : Modules.{u, u} B S hS X.1 X.2} (g : X ⟶ X')
    (x : M ⟶ (smallEtaleRingedToposHom B S hS g).pushforwardModules.obj N) :
    (modulePullbackAdjunction B S hS g).homEquiv M N
        (((smallEtaleRingedToposHom B S hS g).pullbackAdjPushforwardModulesViaComparison.homEquiv
          M N).symm x) =
      x ≫ (pushforwardModulesIsoModulePushforward B S hS g).hom.app N :=
  homEquiv_ofNatIsoRight_trans_symm
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
      (smallEtaleRingedToposModulesHom B S hS g))
    (smallEtaleRingedToposHom B S hS g).pushforwardModulesIso
    (pushforwardModulesIsoModulePushforward B S hS g) x

/-- **The degree-`n` component of the ambient homomorphism of Stacks 09RS is the transpose of
pullback of regular functions**: its chartwise transpose is
`AlgebraicGeometry.Space.kernelIdealSheafZPowFMapOfEq`. -/
theorem modulePullbackHomFMap_kernelIdealGradedPullbackHom_app (i : Z ⟶ X) (g : X ⟶ X')
    (j : Z ⟶ X') (hj : i ≫ g = j) (n : ℤ) :
    modulePullbackHomFMap B S hS g _ _ ((kernelIdealGradedPullbackHom B S hS i g j hj).app n) =
      kernelIdealSheafZPowFMapOfEq B S hS i g j hj n := by
  have h1 := kernelIdealGradedPullbackHom_app_eq B S hS i g j hj n
  have h2 := modulePullbackAdjunction_homEquiv_viaComparison_symm B S hS g
    ((kernelIdealGradedPushforwardHom B S hS i g j hj).app n)
  have h3 : (modulePullbackAdjunction B S hS g).homEquiv _ _
      ((kernelIdealGradedPullbackHom B S hS i g j hj).app n) =
        (modulePushforwardHomEquiv B S hS g _ _).symm
          (kernelIdealSheafZPowFMapOfEq B S hS i g j hj n) := by
    rw [h1, h2]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id_app _ _)).trans
      (Category.comp_id _))
  exact (congrArg (modulePushforwardHomEquiv B S hS g _ _) h3).trans (Equiv.apply_symm_apply _ _)

/-- **The value of the degree-`n` component of the ambient homomorphism of Stacks 09RS on a unit
section is pullback of regular functions.** -/
theorem kernelIdealGradedPullbackHom_app_modulePullbackUnitSection_coe (i : Z ⟶ X)
    (g : X ⟶ X') (j : Z ⟶ X') (hj : i ≫ g = j) (n : ℤ)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (t : (kernelIdealSheafZPow B S hS j n).toSheafOfModules.val.obj (op d.V)) :
    (((kernelIdealGradedPullbackHom B S hS i g j hj).app n).val.app (op d.U)
        (modulePullbackUnitSection B S hS g _ d t)).1 =
      (chartDiagramPullback B S hS g d).hom t.1 := by
  have h := (modulePullbackHomFMap_app B S hS g _ _
    ((kernelIdealGradedPullbackHom B S hS i g j hj).app n) d t).symm.trans
    (congrArg (fun ξ : ModuleFMap B S hS g (kernelIdealSheafZPow B S hS i n).toSheafOfModules
        (kernelIdealSheafZPow B S hS j n).toSheafOfModules => ξ.app d t)
      (modulePullbackHomFMap_kernelIdealGradedPullbackHom_app B S hS i g j hj n))
  exact congrArg Subtype.val h

/-- **The ambient comparison of the canonical map of Stacks 09RS is induced by pullback of
regular functions in every degree**: its value on the unit section of a section of `(𝓘')ⁿ` is
the pullback of that section. -/
theorem isInducedByPullback_conormalAlgebraSquareAmbientComparison_app (i : Z ⟶ X)
    (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    IsInducedByPullback B S hS i i' g n
      ((conormalAlgebraSquareAmbientComparison B S hS i i' f g
        (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq)).app n) := by
  intro d s
  have hnat := modulePullbackUnitSection_naturality_module B S hS g
    ((kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl).app n) d s
  have hval := kernelIdealGradedPullbackHom_app_modulePullbackUnitSection_coe B S hS i g (f ≫ i')
    hsq n d (((kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl).app n).val.app (op d.V) s)
  have hcoe := SheafOfModules.reesGradedAlgebraHomOfLe_app_coe (kernelIdealSheaf B S hS i')
    (kernelIdealSheaf B S hS (f ≫ i')) (structureRingSheaf_mul_comm B S hS X')
    (kernelIdealSheaf_le_comp B S hS f i' f i' rfl) n (op d.V) s
  rw [conormalAlgebraSquareAmbientComparison_app]
  change ((((kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq).app n).val.app (op d.U)
      (((modulePullback B S hS g).map
        ((kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl).app n)).val.app (op d.U)
          (modulePullbackUnitSection B S hS g _ d s)))).1 = _
  rw [← hnat]
  exact hval.trans (congrArg (chartDiagramPullback B S hS g d).hom hcoe)

/-! ### Vanishing in negative degrees -/

/-- In a negative degree the power of a kernel ideal sheaf is the zero module. -/
theorem isZero_kernelIdealSheafZPow_of_neg {Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) {n : ℤ}
    (hn : n < 0) : IsZero (kernelIdealSheafZPow B S hS p n).toSheafOfModules := by
  have hbot : ∀ U, SheafOfModules.idealAt (kernelIdealSheafZPow B S hS p n) U = ⊥ := fun U => by
    rw [kernelIdealSheafZPow_of_neg B S hS p hn, SheafOfModules.idealAt_zeroIdealSheaf]
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext U x
  refine Subtype.ext ?_
  exact (SheafOfModules.eq_zero_of_mem_bot ((hbot U) ▸ x.2)).trans
    (SheafOfModules.eq_zero_of_mem_bot ((hbot U) ▸ (0 : (kernelIdealSheafZPow B S hS p n
      ).toSheafOfModules.val.obj U).2)).symm

/-- The inverse image of modules preserves zero objects, being a left adjoint. -/
theorem isZero_modulePullback_obj {W V : AlgebraicSpaces B S hS} (a : W ⟶ V)
    {M : Modules.{u, u} B S hS V.1 V.2} (hM : IsZero M) :
    IsZero ((modulePullback B S hS a).obj M) :=
  have : (modulePullback B S hS a).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS a).isLeftAdjoint
  Functor.map_isZero _ hM

/-! ### Stacks 09RT -/

variable {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'}

/-- **[Stacks Project, Tag 09RT], surjectivity.**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a cartesian square of algebraic spaces with `i'` (hence `i`) an immersion.  Then the canonical
map `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS] is surjective: it is an
epimorphism of `𝒪_Z`-modules in every degree.

In degree `n ≥ 0` the map is the inverse image along `i` of the degree-`n` ambient comparison,
preceded by two isomorphisms; that comparison is induced by pullback of regular functions
(`AlgebraicGeometry.Space.isInducedByPullback_conormalAlgebraSquareAmbientComparison_app`), so its
inverse image along `i` is an epimorphism by
`AlgebraicGeometry.Space.epi_modulePullback_map_of_isPullback`.  In negative degrees the target
vanishes. -/
@[stacks 09RT "surjectivity: for a cartesian square with i' (hence i) an immersion, the \
canonical map f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*} of Tag 09RS is surjective in every degree"]
theorem epi_conormalAlgebraSquareMap_app_of_isPullback (sq : IsPullback i f g i')
    (hi' : IsImmersion B S hS i'.hom) (n : ℤ) :
    Epi ((conormalAlgebraSquareMap B S hS i i' f g sq.w).app n) := by
  rcases lt_or_ge n 0 with hn | hn
  · exact IsZero.epi (isZero_modulePullback_obj B S hS i
      (isZero_kernelIdealSheafZPow_of_neg B S hS i hn)) _
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h₁ := SheafOfModules.GradedAlgebra.isIso_app_of_isIso
      (((gradedAlgebraPullbackCompIso B S hS f i').app
        (kernelIdealGradedAlgebra B S hS i')).inv) inferInstance (m : ℤ)
    have h₂ := SheafOfModules.GradedAlgebra.isIso_app_of_isIso
      (((gradedAlgebraPullbackCompIsoOfEq B S hS i g (f ≫ i') sq.w.symm).app
        (kernelIdealGradedAlgebra B S hS i')).hom) inferInstance (m : ℤ)
    have h₃ := epi_modulePullback_map_of_isPullback B S hS sq hi' m
      ((conormalAlgebraSquareAmbientComparison B S hS i i' f g
        (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') sq.w)).app (m : ℤ))
      (isInducedByPullback_conormalAlgebraSquareAmbientComparison_app B S hS i i' f g sq.w m)
    rw [conormalAlgebraSquareMap, conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ h₁) _
      (@epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ h₂) _ h₃)

/-- The canonical map of Stacks 09RS is an isomorphism in every degree when the square is
cartesian, `i'` is an immersion and `g` is flat. -/
theorem isIso_conormalAlgebraSquareMap_app_of_isPullback_of_isFlat (sq : IsPullback i f g i')
    (hi' : IsImmersion B S hS i'.hom) (hg : IsFlat B S hS g.hom) (n : ℤ) :
    IsIso ((conormalAlgebraSquareMap B S hS i i' f g sq.w).app n) := by
  rcases lt_or_ge n 0 with hn | hn
  · exact IsZero.isIso (isZero_modulePullback_obj B S hS f (isZero_modulePullback_obj B S hS i'
      (isZero_kernelIdealSheafZPow_of_neg B S hS i' hn)))
      (isZero_modulePullback_obj B S hS i (isZero_kernelIdealSheafZPow_of_neg B S hS i hn)) _
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h₁ := SheafOfModules.GradedAlgebra.isIso_app_of_isIso
      (((gradedAlgebraPullbackCompIso B S hS f i').app
        (kernelIdealGradedAlgebra B S hS i')).inv) inferInstance (m : ℤ)
    have h₂ := SheafOfModules.GradedAlgebra.isIso_app_of_isIso
      (((gradedAlgebraPullbackCompIsoOfEq B S hS i g (f ≫ i') sq.w.symm).app
        (kernelIdealGradedAlgebra B S hS i')).hom) inferInstance (m : ℤ)
    have h₃ := isIso_modulePullback_map_of_isPullback_of_isFlat B S hS sq hi' hg m
      ((conormalAlgebraSquareAmbientComparison B S hS i i' f g
        (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') sq.w)).app (m : ℤ))
      (isInducedByPullback_conormalAlgebraSquareAmbientComparison_app B S hS i i' f g sq.w m)
    rw [conormalAlgebraSquareMap, conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₃)

/-- **[Stacks Project, Tag 09RT], the flat case.**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a cartesian square of algebraic spaces with `i'` (hence `i`) an immersion.  If `g` is flat,
the canonical map `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS] is an isomorphism
of sheaves of graded `𝒪_Z`-algebras.

Degreewise this is
`AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMap_app_of_isPullback_of_isFlat`, whose
nonnegative degrees are `AlgebraicGeometry.Space.isIso_modulePullback_map_of_isPullback_of_isFlat`
for the ambient comparison; a degreewise isomorphism of sheaves of graded algebras is an
isomorphism. -/
@[stacks 09RT "flat case: for a cartesian square with i' (hence i) an immersion and g flat, the \
canonical map f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*} of Tag 09RS is an isomorphism of graded algebras"]
theorem isIso_conormalAlgebraSquareMap_of_isPullback_of_isFlat (sq : IsPullback i f g i')
    (hi' : IsImmersion B S hS i'.hom) (hg : IsFlat B S hS g.hom) :
    IsIso (conormalAlgebraSquareMap B S hS i i' f g sq.w) :=
  SheafOfModules.GradedAlgebra.isIso_of_forall_isIso_app _
    (isIso_conormalAlgebraSquareMap_app_of_isPullback_of_isFlat B S hS sq hi' hg)

end AlgebraicGeometry.Space

end
