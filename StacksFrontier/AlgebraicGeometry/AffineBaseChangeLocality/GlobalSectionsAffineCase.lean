module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.Pasting
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.Reduction

/-!
# The affine base-change comparison on global sections

For a commutative square of spectra
```
Spec B' --Spec ψ'--> Spec B
|Spec φ'             |Spec φ
Spec A' --Spec ψ-->  Spec A
```
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase` reduces the base-change
assertion of Stacks Tag 02KG to the question of what the base-change morphism does on global
sections, and answers it for the module-theoretic half: a map `A' ⊗_A M ⟶ B' ⊗_B M` carrying
`1 ⊗ m` to `1 ⊗ m` is bijective when `B' = B ⊗_A A'`.  This file supplies the missing
geometric half, namely that the global-sections comparison *is* such a map.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.moduleSpecΓ_map_baseChangeNatTrans_unit`:
  on global sections the base-change morphism of a square of spectra carries the unit of the
  pullback--pushforward adjunction along the bottom morphism to the unit along the top
  morphism.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.sectionsSquareComparison_one_tmul`: the
  five-fold global-sections comparison of a square of spectra carries `1 ⊗ m` to `1 ⊗ m`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_of_one_tmul`: an `A'`-linear map
  `A' ⊗_A M ⟶ B' ⊗_B M` carrying `1 ⊗ m` to `1 ⊗ m` is invertible when the square of rings is
  a pushout.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_specSquare`: the
  base-change morphism of a square of spectra whose square of rings is a pushout is invertible
  at every quasi-coherent module.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_of_isIso_horiz`:
  the base-change morphism of a square whose horizontal morphisms are isomorphisms is
  invertible.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_of_isAffine`: the
  affine case of the base-change assertion, for an arbitrary cartesian square of affine
  schemes.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans` and
  `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso`: Stacks Tag 02KG assertion
  3 itself, unconditionally.

## Implementation notes

The two `A`-module structures on `Γ(𝓕, ⊤)` -- the one coming from the direct image along
`Spec φ` and the one coming from restriction of scalars along `φ` -- are equal but not
definitionally equal, so the tensor products `A' ⊗_A Γ(𝓕, ⊤)` formed from them are genuinely
different types.  That is what the first factor of the comparison, the image under
`ModuleCat.extendScalars` of `Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso`, is
for; it is the identity on elements, so `ModuleCat.ExtendScalars.map_tmul` moves a pure tensor
across it by `rfl`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeLocality

variable {A B A' B' : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ A') (ψ' : B ⟶ B') (φ' : A' ⟶ B')

/-- **The module-theoretic affine base-change comparison is invertible.**  If the square of
rings `A → B`, `A → A'`, `B → B'`, `A' → B'` is a pushout, then an `A'`-linear map
`A' ⊗_A M ⟶ B' ⊗_B M` carrying `1 ⊗ m` to `1 ⊗ m` is an isomorphism: it agrees with
`Algebra.IsPushout.cancelBaseChange`, by `ModuleCat.ExtendScalars.hom_ext`. -/
theorem isIso_of_one_tmul (hpush : IsPushout φ ψ ψ' φ') (M : ModuleCat.{u} B)
    (Θ : (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj M) ⟶
      (ModuleCat.restrictScalars φ'.hom).obj ((ModuleCat.extendScalars ψ'.hom).obj M))
    (hΘ : ∀ m : M, Θ.hom ((1 : A') ⊗ₜ[A, ψ.hom] m) = ((1 : B') ⊗ₜ[B, ψ'.hom] m)) :
    IsIso Θ := by
  let iAA' : Algebra A A' := ψ.hom.toAlgebra
  let iAB : Algebra A B := φ.hom.toAlgebra
  let iBB' : Algebra B B' := ψ'.hom.toAlgebra
  let iA'B' : Algebra A' B' := φ'.hom.toAlgebra
  let iAB' : Algebra A B' := (φ'.hom.comp ψ.hom).toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq (fun x =>
    (congr($(hpush.w).hom x)).symm)
  have : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.mp hpush
  have : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  let iAM : Module A M := Module.compHom M φ.hom
  have : IsScalarTower A B M := ⟨fun a b m => mul_smul (φ.hom a) b m⟩
  let Ξ : (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (ModuleCat.restrictScalars φ'.hom).obj ((ModuleCat.extendScalars ψ'.hom).obj M) :=
    LinearEquiv.toModuleIso (Algebra.IsPushout.cancelBaseChange A A' B B' M).symm
  have hΘΞ : Θ = Ξ.hom := by
    refine ModuleCat.ExtendScalars.hom_ext (fun m => ?_)
    refine (hΘ m).trans ?_
    exact ((LinearEquiv.symm_apply_eq _).2
      (Algebra.IsPushout.cancelBaseChange_tmul A A' B B' M m).symm).symm
  rw [hΘΞ]
  infer_instance

/-- On sections over the whole space, the base-change morphism of a commutative square of
spectra carries the canonical map `Γ(𝓕, ⊤) ⟶ Γ((Spec ψ)^* (Spec φ)_* 𝓕, ⊤)` to the canonical
map `Γ(𝓕, ⊤) ⟶ Γ((Spec ψ')^* 𝓕, ⊤)`.  This is
`Stacks.AlgebraicGeometry.AffineBaseChange.app_top_unit_comp_baseChangeNatTrans` read
elementwise. -/
theorem moduleSpecΓ_map_baseChangeNatTrans_unit
    (w : Spec.map ψ' ≫ Spec.map φ = Spec.map φ' ≫ Spec.map ψ) (F : (Spec B).Modules)
    (y : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj F)) :
    (moduleSpecΓFunctor.map ((AffinePushforward.baseChangeNatTrans w).app F)).hom
        ((moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map ψ)).unit.app ((Scheme.Modules.pushforward (Spec.map φ)).obj F))).hom y) =
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map ψ')).unit.app F)).hom y := by
  have key := AffineBaseChange.app_top_unit_comp_baseChangeNatTrans w F
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    TopologicalSpace.Opens.map_top] at key
  exact congr($key y)

/-- The five-fold global-sections comparison attached to a commutative square of spectra
carries `1 ⊗ m` to `1 ⊗ m`.  Its factors are, in order: the comparison of the two `A`-module
structures on `Γ(𝓕, ⊤)`, the identification of the sections of an inverse image along
`Spec ψ` with `A' ⊗_A -`, the base-change morphism on global sections, the comparison of the
two `A'`-module structures on `Γ((Spec ψ')^* 𝓕, ⊤)`, and the identification of the sections of
an inverse image along `Spec ψ'` with `B' ⊗_B -`. -/
theorem sectionsSquareComparison_one_tmul
    (w : Spec.map ψ' ≫ Spec.map φ = Spec.map φ' ≫ Spec.map ψ) (F : (Spec B).Modules)
    [F.IsQuasicoherent]
    [((Scheme.Modules.pushforward (Spec.map φ)).obj F).IsQuasicoherent]
    (y : moduleSpecΓFunctor.obj F) :
    ((ModuleCat.extendScalars ψ.hom).map
            ((SectionsColimit.pullbackSectionsIso φ).inv.app F) ≫
          (SectionsColimit.sectionsPullbackIso ψ
            ((Scheme.Modules.pushforward (Spec.map φ)).obj F)).inv ≫
          moduleSpecΓFunctor.map ((AffinePushforward.baseChangeNatTrans w).app F) ≫
          (SectionsColimit.pullbackSectionsIso φ').hom.app
            ((Scheme.Modules.pullback (Spec.map ψ')).obj F) ≫
          (ModuleCat.restrictScalars φ'.hom).map (SectionsColimit.sectionsPullbackIso ψ' F).hom).hom
        ((1 : A') ⊗ₜ[A, ψ.hom] toRestrictScalars φ.hom y) =
      (1 : B') ⊗ₜ[B, ψ'.hom] y := by
  have h5 := sectionsPullbackIso_hom_unit ψ' F y _ rfl
  have h2 :=
    sectionsPullbackIso_hom_unit ψ ((Scheme.Modules.pushforward (Spec.map φ)).obj F) y _ rfl
  have h3 := moduleSpecΓ_map_baseChangeNatTrans_unit φ ψ ψ' φ' w F y
  refine Eq.trans ?_ h5
  refine congrArg (SectionsColimit.sectionsPullbackIso ψ' F).hom.hom ?_
  refine Eq.trans ?_ h3
  refine congrArg (moduleSpecΓFunctor.map ((AffinePushforward.baseChangeNatTrans w).app F)).hom ?_
  have hone : ((ModuleCat.extendScalars ψ.hom).map
        ((SectionsColimit.pullbackSectionsIso φ).inv.app F)).hom
        ((1 : A') ⊗ₜ[A, ψ.hom] toRestrictScalars φ.hom y) =
      (SectionsColimit.sectionsPullbackIso ψ
          ((Scheme.Modules.pushforward (Spec.map φ)).obj F)).hom.hom
        ((moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map ψ)).unit.app ((Scheme.Modules.pushforward (Spec.map φ)).obj F))).hom y) :=
    h2.symm
  refine Eq.trans (congrArg (SectionsColimit.sectionsPullbackIso ψ
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F)).inv.hom hone) ?_
  exact congr(ModuleCat.Hom.hom $((SectionsColimit.sectionsPullbackIso ψ
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F)).hom_inv_id) _)

/-! ### Glue -/

/-- If a five-fold composite is invertible and the four outer factors are invertible, then so
is the middle factor.  The invertibility hypotheses are explicit arguments rather than
instances: the two category structures on sheaves of modules over a scheme are equal only
after unfolding a non-reducible definition, which instance search does not do. -/
theorem isIso_middle_of_isIso_comp {C : Type*} [Category C] {M₁ M₂ M₃ M₄ M₅ M₆ : C}
    {a : M₁ ⟶ M₂} {b : M₂ ⟶ M₃} {c : M₃ ⟶ M₄} {d : M₄ ⟶ M₅} {e : M₅ ⟶ M₆}
    (ha : IsIso a) (hb : IsIso b) (hd : IsIso d) (he : IsIso e)
    (h : IsIso (a ≫ b ≫ c ≫ d ≫ e)) : IsIso c :=
  have h1 : IsIso (b ≫ c ≫ d ≫ e) := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ha h
  have h2 : IsIso (c ≫ d ≫ e) := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hb h1
  have hde : IsIso (d ≫ e) := @IsIso.comp_isIso _ _ _ _ _ _ _ hd he
  @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hde h2

/-- **The affine case of base change for the direct image**, Stacks Tag 02KG assertion 3, for a
commutative square of spectra whose underlying square of rings is a pushout: the canonical
base-change morphism is invertible at every quasi-coherent module.  Both sides are
quasi-coherent, so by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` it suffices to check
invertibility on global sections, where the morphism is the middle factor of the comparison of
`sectionsSquareComparison_one_tmul`. -/
theorem isIso_baseChangeNatTrans_specSquare (hpush : IsPushout φ ψ ψ' φ')
    (w : Spec.map ψ' ≫ Spec.map φ = Spec.map φ' ≫ Spec.map ψ) (F : (Spec B).Modules)
    [F.IsQuasicoherent] : IsIso ((AffinePushforward.baseChangeNatTrans w).app F) := by
  have hp : ((Scheme.Modules.pushforward (Spec.map φ)).obj F).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_specMap _ F
  have hL : ((Scheme.Modules.pushforward (Spec.map φ) ⋙
      Scheme.Modules.pullback (Spec.map ψ)).obj F).IsQuasicoherent :=
    SectionsColimit.isQuasicoherent_pullback_specMap _ _
  have hR₀ : ((Scheme.Modules.pushforward (Spec.map φ')).obj
      ((Scheme.Modules.pullback (Spec.map ψ')).obj F)).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_specMap _ _
  have hR : ((Scheme.Modules.pullback (Spec.map ψ') ⋙
      Scheme.Modules.pushforward (Spec.map φ')).obj F).IsQuasicoherent := hR₀
  refine AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ ?_
  have hmid := isIso_of_one_tmul φ ψ ψ' φ' hpush (moduleSpecΓFunctor.obj F) _
    (sectionsSquareComparison_one_tmul φ ψ ψ' φ' w F)
  refine isIso_middle_of_isIso_comp ?_ ?_ ?_ ?_ hmid
  · exact Functor.map_isIso _ _
  · exact Iso.isIso_inv _
  · exact NatIso.isIso_app_of_isIso _ _
  · exact Functor.map_isIso _ _

/-- If a five-fold composite of morphisms of modules is bijective and the four outer factors
are invertible, then the middle factor is bijective. -/
theorem bijective_middle_of_bijective_comp {R : Type u} [Ring R]
    {M₁ M₂ M₃ M₄ M₅ M₆ : ModuleCat.{u} R} {a : M₁ ⟶ M₂} {b : M₂ ⟶ M₃} {c : M₃ ⟶ M₄}
    {d : M₄ ⟶ M₅} {e : M₅ ⟶ M₆} (ha : IsIso a) (hb : IsIso b) (hd : IsIso d) (he : IsIso e)
    (h : Function.Bijective (a ≫ b ≫ c ≫ d ≫ e).hom) : Function.Bijective c.hom :=
  (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_middle_of_isIso_comp ha hb hd he ((ConcreteCategory.isIso_iff_bijective _).2 h))

section SpecTensor

variable (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']

/-- The global-sections comparison of the affine base-change square carries `1 ⊗ m` to
`1 ⊗ m`.  This is the hypothesis of
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.bijective_of_one_tmul`. -/
theorem sectionsComparison_tmulA_one (F : (Spec (CommRingCat.of B)).Modules)
    [F.IsQuasicoherent]
    (h1 : ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F).IsQuasicoherent)
    (y : moduleSpecΓFunctor.obj F) :
    (sectionsComparison A B A' F h1).hom (tmulA (1 : A') y) = tmulB (1 : B ⊗[A] A') y := by
  have : ((Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F).IsQuasicoherent := h1
  exact sectionsSquareComparison_one_tmul _ _ _ _ (specTensor_square A B A') F y

/-- **The affine case of base change for the direct image**, Stacks Tag 02KG assertion 3, for
the square of spectra attached to `A → B` and `A → A'` with upper-left corner
`Spec (B ⊗[A] A')`: the canonical base-change morphism is invertible at every quasi-coherent
module. -/
theorem isIso_baseChangeNatTrans_specTensor (F : (Spec (CommRingCat.of B)).Modules)
    [F.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans (specTensor_square A B A')).app F) := by
  have h1 : ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_specMap _ F
  have hbij := bijective_of_one_tmul (sectionsComparison A B A' F h1)
    (sectionsComparison_tmulA_one A B A' F h1)
  refine isIso_baseChangeNatTrans_specTensor_of_bijective A B A' F ?_
  exact bijective_middle_of_bijective_comp
    (a := (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).map
      ((SectionsColimit.pullbackSectionsIso (CommRingCat.ofHom (algebraMap A B))).inv.app F))
    (b := (SectionsColimit.sectionsPullbackIso (CommRingCat.ofHom (algebraMap A A'))
      ((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F)).inv)
    (d := (SectionsColimit.pullbackSectionsIso (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom)).hom.app
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))))).obj F))
    (e := (ModuleCat.restrictScalars (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom).hom).map
      (SectionsColimit.sectionsPullbackIso (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))) F).hom)
    (Functor.map_isIso _ _) (Iso.isIso_inv _) (NatIso.isIso_app_of_isIso _ _)
    (Functor.map_isIso _ _) hbij

end SpecTensor

/-! ### Base change along a square of isomorphisms -/

/-- The inverse image of sheaves of modules along an isomorphism of schemes is faithful. -/
instance pullback_faithful_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    (Scheme.Modules.pullback e).Faithful :=
  Functor.Faithful.of_comp_iso (G := Scheme.Modules.pullback (inv e))
    (Scheme.Modules.pullbackComp (inv e) e ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id e) ≪≫ Scheme.Modules.pullbackId Y)

/-- The inverse image of sheaves of modules along an isomorphism of schemes is full. -/
instance pullback_full_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    (Scheme.Modules.pullback e).Full :=
  Functor.Full.of_comp_faithful_iso (G := Scheme.Modules.pullback (inv e))
    (Scheme.Modules.pullbackComp (inv e) e ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id e) ≪≫ Scheme.Modules.pullbackId Y)

/-- The direct image of sheaves of modules along an isomorphism of schemes is faithful. -/
instance pushforward_faithful_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    (Scheme.Modules.pushforward e).Faithful :=
  Functor.Faithful.of_comp_iso (G := Scheme.Modules.pushforward (inv e))
    (Scheme.Modules.pushforwardComp e (inv e) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id e) ≪≫ Scheme.Modules.pushforwardId X)

/-- The direct image of sheaves of modules along an isomorphism of schemes is full. -/
instance pushforward_full_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    (Scheme.Modules.pushforward e).Full :=
  Functor.Full.of_comp_faithful_iso (G := Scheme.Modules.pushforward (inv e))
    (Scheme.Modules.pushforwardComp e (inv e) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id e) ≪≫ Scheme.Modules.pushforwardId X)

/-- The three factors of a mate: the image under the lower left adjoint of the image under the
left-hand functor of the unit of the upper adjunction, the image under the lower left adjoint
of the given 2-cell, and the counit of the lower adjunction. -/
theorem mateEquiv_symm_natTrans_app {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂) (c : C) :
    ((mateEquiv adj₁ adj₂).symm α).app c =
      L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (α.app (L₁.obj c)) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
  simp [mateEquiv]

section IsoSquare

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The three factors of the canonical base-change morphism of a commutative square: the image
under `g^*` of the direct image along `f` of the unit of the pullback--pushforward adjunction
along `g'`, the image under `g^*` of the identification of the two composite direct images
around the square, and the counit of the pullback--pushforward adjunction along `g`. -/
theorem baseChangeNatTrans_app_eq (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (AffinePushforward.baseChangeNatTrans w).app M =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M)) ≫
        (Scheme.Modules.pullback g).map
          ((AffinePushforward.pushforwardSquareIso w).hom.app
            ((Scheme.Modules.pullback g').obj M)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
          ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj M)) := by
  rw [AffinePushforward.baseChangeNatTrans_eq w]
  exact mateEquiv_symm_natTrans_app (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom) M

/-- **Base change along a square of isomorphisms.**  If the two horizontal morphisms of a
commutative square of schemes are isomorphisms, its canonical base-change morphism is
invertible at every sheaf of modules.  No quasi-coherence is needed: the inverse image along
an isomorphism is fully faithful, so the unit of its adjunction is invertible, and likewise
the direct image is fully faithful, so the counit is invertible; the middle factor of
`baseChangeNatTrans_app_eq` is the image of an isomorphism. -/
theorem isIso_baseChangeNatTrans_of_isIso_horiz (w : g' ≫ f = f' ≫ g) [IsIso g] [IsIso g']
    (M : X.Modules) : IsIso ((AffinePushforward.baseChangeNatTrans w).app M) := by
  have hu : IsIso (Scheme.Modules.pullbackPushforwardAdjunction g').unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hc : IsIso (Scheme.Modules.pullbackPushforwardAdjunction g).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  have hu' : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M) :=
    NatIso.isIso_app_of_isIso _ M
  have a1 : IsIso ((Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M))) :=
    Functor.map_isIso _ _
  have a2 : IsIso ((Scheme.Modules.pullback g).map
      ((AffinePushforward.pushforwardSquareIso w).hom.app
        ((Scheme.Modules.pullback g').obj M))) :=
    Functor.map_isIso _ _
  have a3 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
      ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj M))) :=
    NatIso.isIso_app_of_isIso _ _
  rw [baseChangeNatTrans_app_eq w M]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ a1 (@IsIso.comp_isIso _ _ _ _ _ _ _ a2 a3)

end IsoSquare

/-! ### The affine case -/

/-- **The affine case of base change for the direct image**, Stacks Tag 02KG assertion 3: for a
cartesian square of affine schemes the canonical base-change morphism
`q^* p_* 𝓖 ⟶ p'_* (q')^* 𝓖` is invertible at every quasi-coherent module `𝓖`.

The square of global sections is a pushout of rings
(`AlgebraicGeometry.isPushout_appTop_of_isPullback`), so
`isIso_baseChangeNatTrans_specSquare` applies to the square of spectra of the maps on global
sections.  The given square is carried into that one by pasting twice with the squares
expressing the naturality of `AlgebraicGeometry.Scheme.isoSpec`, whose horizontal morphisms
are isomorphisms; `isIso_baseChangeNatTrans_of_isIso_horiz` handles those, and the pasting
transfers invertibility by the lemmas of
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.Pasting`. -/
theorem isIso_baseChangeNatTrans_of_isAffine {Y' Y T' T : Scheme.{u}} [IsAffine Y'] [IsAffine Y]
    [IsAffine T'] [IsAffine T] {q' : Y' ⟶ Y} {p' : Y' ⟶ T'} {p : Y ⟶ T} {q : T' ⟶ T}
    (hp : IsPullback q' p' p q) (G : Y.Modules) (hG : G.IsQuasicoherent) :
    IsIso ((AffinePushforward.baseChangeNatTrans hp.w).app G) := by
  have hGi : G.IsQuasicoherent := hG
  have hpush := isPushout_appTop_of_isPullback hp
  have wS : Spec.map q'.appTop ≫ Spec.map p.appTop
      = Spec.map p'.appTop ≫ Spec.map q.appTop := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpush.w]
  have wL := (Scheme.isoSpec_inv_naturality p').symm
  have wR := (Scheme.isoSpec_inv_naturality p).symm
  have wq' := (Scheme.isoSpec_inv_naturality q').symm
  have wq := (Scheme.isoSpec_inv_naturality q).symm
  have wab2 : (Spec.map q'.appTop ≫ Y.isoSpec.inv) ≫ p
      = Spec.map p'.appTop ≫ (Spec.map q.appTop ≫ T.isoSpec.inv) := by
    rw [Category.assoc, wR, ← Category.assoc, wS, Category.assoc]
  have wab1 : (Y'.isoSpec.inv ≫ q') ≫ p = Spec.map p'.appTop ≫ (T'.isoSpec.inv ≫ q) := by
    rwa [wq', wq]
  have hqcY : ((Scheme.Modules.pullback Y.isoSpec.inv).obj G).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback Y.isoSpec.inv G
  have ha2 : IsIso ((AffinePushforward.baseChangeNatTrans wS).app
      ((Scheme.Modules.pullback Y.isoSpec.inv).obj G)) :=
    isIso_baseChangeNatTrans_specSquare _ _ _ _ hpush wS _
  have hwR : IsIso ((AffinePushforward.baseChangeNatTrans wR).app G) :=
    isIso_baseChangeNatTrans_of_isIso_horiz wR G
  have hbR : IsIso ((Scheme.Modules.pullback (Spec.map q.appTop)).map
      ((AffinePushforward.baseChangeNatTrans wR).app G)) := Functor.map_isIso _ _
  have hab2 : IsIso ((AffinePushforward.baseChangeNatTrans wab2).app G) :=
    isIso_baseChangeNatTrans_vcomp wS wR wab2 G hbR ha2
  have hab1 : IsIso ((AffinePushforward.baseChangeNatTrans wab1).app G) :=
    isIso_baseChangeNatTrans_congr wq'.symm wq.symm wab2 wab1 G hab2
  have hwL : IsIso ((AffinePushforward.baseChangeNatTrans wL).app
      ((Scheme.Modules.pullback q').obj G)) :=
    isIso_baseChangeNatTrans_of_isIso_horiz wL _
  have hmap : IsIso ((Scheme.Modules.pullback T'.isoSpec.inv).map
      ((AffinePushforward.baseChangeNatTrans hp.w).app G)) :=
    isIso_map_baseChangeNatTrans_of_vcomp wL hp.w wab1 G hwL hab1
  exact isIso_of_reflects_iso _ (Scheme.Modules.pullback T'.isoSpec.inv)

/-! ### Stacks Tag 02KG, assertion 3 -/

/-- **Stacks Tag 02KG, assertion 3.**  For a cartesian square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `f` affine and `𝓕` quasi-coherent on `X`, the canonical base-change morphism
`g^* f_* 𝓕 ⟶ f'_* (g')^* 𝓕` is an isomorphism.  This is
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_of_affineCase` with
its affine-case hypothesis discharged by `isIso_baseChangeNatTrans_of_isAffine`.

No `@[stacks 02KG]` attribute is placed here: Tag 02KG has three assertions, and the covering
set is not complete until the degeneration `Rf_* 𝓕 ≅ f_* 𝓕` is also formalized. -/
theorem isIso_baseChangeNatTrans {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g) [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] : IsIso ((AffinePushforward.baseChangeNatTrans h.w).app F) :=
  isIso_baseChangeNatTrans_of_affineCase h F
    (fun hp _ G hG => isIso_baseChangeNatTrans_of_isAffine hp G hG)

/-- **Stacks Tag 02KG, assertion 3**, packaged as the bare isomorphism of modules, in the shape
in which the consumers of the base-change assertion thread it as a hypothesis. -/
noncomputable def baseChangeIso :
    ∀ {Y' Y T' T : Scheme.{u}} (q' : Y' ⟶ Y) (p' : Y' ⟶ T') (p : Y ⟶ T) (q : T' ⟶ T),
      IsPullback q' p' p q → IsAffineHom p → ∀ G : Y.Modules, G.IsQuasicoherent →
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward p).obj G) ≅
        (Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback q').obj G)) :=
  baseChangeIso_of_affineCase (fun hp _ G hG => isIso_baseChangeNatTrans_of_isAffine hp G hG)

end Stacks.AlgebraicGeometry.AffineBaseChangeLocality

end
