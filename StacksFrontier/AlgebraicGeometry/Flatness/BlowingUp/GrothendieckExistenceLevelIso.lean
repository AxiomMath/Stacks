module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceOpenNeighbourhood
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# Part (3) of Stacks 0CTH

In Situation [Stacks, Tag 0CTC], let `K` be the object of [Stacks, Tag 0CTD] and `W ⊇ X₀` an open
on which `K` has cohomology only in degree zero, with `ℱ = H⁰(K)|_W`. Part (3) of
[Stacks, Tag 0CTH] says that the canonical maps `ℱ ⊗ 𝒪_{Xₙ} ⟶ ℱₙ` are isomorphisms. Over an
affine open `U ⊆ W`, [Stacks, Tag 0CTG] identifies `Γ(U, ℱ) ⊗_A Aₙ` with `Γ(Uₙ, ℱₙ)`, and the
canonical map on sections over `Uₙ` is read off from this identification.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.isIso_of_isIso_homEquiv_symm_comp`: the algebraic step.
  For a surjective ring map `A ⟶ B`, a surjection `ψ : M ⟶ P` onto an `A`-module which is a
  `B`-module, and a map `ζ : P ⟶ N`, if the base change of `ψ ≫ ζ` to `B` is invertible after
  identifying `N` with a `B`-module, then `ζ` is invertible.

## References

* [Stacks Project, Tag 0CTH](https://stacks.math.columbia.edu/tag/0CTH)
* [Stacks Project, Tag 0CTG](https://stacks.math.columbia.edu/tag/0CTG)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.CoherentTFAE (isQuasicoherent_isFiniteType_of_isFinitePresentation)
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.GrothendieckExistence

/-- Along a surjective ring map `A ⟶ B`, every element of `B ⊗_A M` is `1 ⊗ m`. -/
theorem exists_unit_app_eq_of_surjective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (M : ModuleCat.{u} A)
    (t : (ModuleCat.extendScalars f).obj M) :
    ∃ m : M, (ModuleCat.extendRestrictScalarsAdj f).unit.app M m = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b m =>
    obtain ⟨a, ha⟩ := hf b
    refine ⟨a • m, ?_⟩
    let S' := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
    have h1 : a • (show S' from (1 : B)) = b := by
      rw [ModuleCat.restrictScalars.smul_def]
      exact (mul_one (f a)).trans ha
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    exact (TensorProduct.smul_tmul (R := A) (M := S') (N := M) a
      (show S' from (1 : B)) m).symm.trans (congrArg (fun x : S' => x ⊗ₜ[A] m) h1)
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', map_add _ _ _⟩

/-- Along a surjective ring map `A ⟶ B`, every element of `B ⊗_A M` is `1 ⊗ m`, written as a
pure tensor. -/
theorem exists_one_tmul_eq_of_surjective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (M : ModuleCat.{u} A)
    (t : (ModuleCat.extendScalars f).obj M) :
    ∃ m : M, (1 : B) ⊗ₜ[A, f] m = t := by
  obtain ⟨m, hm⟩ := exists_unit_app_eq_of_surjective f hf M t
  exact ⟨m, (ModuleCat.extendRestrictScalarsAdj_unit_app_apply f M m).symm.trans hm⟩

/-- `AlgebraicGeometry.GrothendieckExistence.exists_one_tmul_eq_of_surjective` for a module given
by its carrier, so that the pure tensors carry the carrier's own module structure. -/
theorem exists_one_tmul_eq_of_surjective_of {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (M : Type u) [AddCommGroup M] [Module A M]
    (t : (ModuleCat.extendScalars f).obj (ModuleCat.of A M)) :
    ∃ m : M, ((1 : B) ⊗ₜ[A, f] m : (ModuleCat.extendScalars f).obj (ModuleCat.of A M)) = t :=
  exists_one_tmul_eq_of_surjective f hf (ModuleCat.of A M) t

/-- The map adjoint to `g : M ⟶ N` along `ModuleCat.extendRestrictScalarsAdj f` sends the image of
`m` under the unit to `g m`. -/
theorem homEquiv_symm_apply_unit_app {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B} (g : M ⟶ (ModuleCat.restrictScalars f).obj N)
    (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app M m) = g m := by
  have h : (ModuleCat.extendRestrictScalarsAdj f).homEquiv M N
      (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g) = g :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k m) h

/-- **The algebraic step of part (3) of [Stacks, Tag 0CTH].** Let `f : A ⟶ B` be a surjective
ring map, `ψ : M ⟶ P` a surjection of `A`-modules and `ζ : P ⟶ N` a map of `A`-modules, where
`P` and `N` are, up to isomorphism, `B`-modules read over `A`. If the map
`B ⊗_A M ⟶ N` adjoint to `ψ ≫ ζ` is invertible, then so is `ζ`. -/
theorem isIso_of_isIso_homEquiv_symm_comp {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) {M P N : ModuleCat.{u} A} {Q N₁ : ModuleCat.{u} B}
    (ψ : M ⟶ P) (hψ : Function.Surjective ψ) (ζ : P ⟶ N)
    (σ : N ≅ (ModuleCat.restrictScalars f).obj N₁) (τ : P ≅ (ModuleCat.restrictScalars f).obj Q)
    (hθ : IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N₁).symm
      (ψ ≫ ζ ≫ σ.hom))) :
    IsIso ζ := by
  set θ := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N₁).symm (ψ ≫ ζ ≫ σ.hom)
  let η := (ModuleCat.extendRestrictScalarsAdj f).unit.app M
  have hθ1 : ∀ m : M, θ (η m) = σ.hom (ζ (ψ m)) := fun m =>
    homEquiv_symm_apply_unit_app f (ψ ≫ ζ ≫ σ.hom) m
  set ψ' := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M Q).symm (ψ ≫ τ.hom)
  have hψ'1 : ∀ m : M, ψ' (η m) = τ.hom (ψ m) := fun m =>
    homEquiv_symm_apply_unit_app f (ψ ≫ τ.hom) m
  have hbij := ConcreteCategory.bijective_of_isIso θ
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, fun y => ?_⟩
  · rw [injective_iff_map_eq_zero ζ.hom]
    intro p hp
    obtain ⟨m, rfl⟩ := hψ p
    have h0 : θ (η m) = θ 0 := by
      rw [hθ1, map_zero]
      show σ.hom (ζ.hom (ψ m)) = 0
      rw [hp, map_zero]
    have h2 : τ.hom (ψ m) = τ.hom 0 := by
      rw [← hψ'1, map_zero]
      simp only [hbij.1 h0]
      exact map_zero _
    exact (ConcreteCategory.bijective_of_isIso τ.hom).1 h2
  · obtain ⟨t, ht⟩ := hbij.2 (σ.hom y)
    obtain ⟨m, rfl⟩ := exists_unit_app_eq_of_surjective f hf M t
    refine ⟨ψ m, ?_⟩
    rw [hθ1] at ht
    exact (ConcreteCategory.bijective_of_isIso σ.hom).1 ht

/-- A family over `ℕᵒᵖ` compatible with the consecutive transitions is compatible with all of
them. -/
theorem map_eq_of_map_succ_eq (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) {m k : ℕ} (h : m ≤ k) :
    F.map (homOfLE h).op (x k) = x m := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl m)).op = 𝟙 (op m) from Subsingleton.elim _ _, F.map_id]
    rfl
  | succ k hmk ih =>
    rw [show (homOfLE (hmk.trans (Nat.le_succ k))).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE hmk).op from Subsingleton.elim _ _,
      F.map_comp, CommRingCat.comp_apply, hx k, ih]

/-- **Sections of a pullback along a closed immersion are pulled back sections.** For a closed
immersion `i : Y ⟶ X`, a quasi-coherent `𝒪_X`-module `F` and an affine open `U` of `X`, every
section of `i^*F` over `i⁻¹U` is the image of a section of `F` over `U` under the unit of
`i^* ⊣ i_*`: `Γ(i⁻¹U, i^*F) = Γ(i⁻¹U, 𝒪_Y) ⊗_{Γ(U, 𝒪_X)} Γ(U, F)` and `Γ(U, 𝒪_X) ⟶ Γ(i⁻¹U, 𝒪_Y)`
is surjective. -/
theorem surjective_unit_app_of_isClosedImmersion {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : IsAffineOpen U) :
    Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).val.app (op U)) := by
  have hV : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hs : Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective U hU
  have hsurj : Function.Surjective
      (Scheme.Modules.pullbackSection i F U (i ⁻¹ᵁ U) le_rfl) := by
    intro y
    obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso
      (affinePullbackSectionsBaseChangeIso i F hU hV le_rfl).hom).2 y
    obtain ⟨m, hm⟩ := exists_one_tmul_eq_of_surjective_of _ hs Γ(F, U) t
    refine ⟨m, (affinePullbackSectionsBaseChangeIso_one_tmul i F hU hV le_rfl m).symm.trans ?_⟩
    rw [← ht, ← hm]
  exact fun y => (hsurj y).imp fun a ha =>
    (Stacks.Conormal.pullbackSection_self i F U a).symm.trans ha

/-- **A map of quasi-coherent modules is invertible if it is so over the preimages of affine
opens.** Let `i : Y ⟶ X` be affine with image inside an open `W`. A map `c` of quasi-coherent
`𝒪_Y`-modules which is bijective on sections over `i⁻¹U` for every affine open `U ⊆ W` is an
isomorphism: these preimages are affine and cover `Y`. -/
theorem isIso_of_bijective_app_preimage {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (c : M ⟶ N) (W : X.Opens)
    (hW : Set.range i ⊆ W)
    (h : ∀ U : X.Opens, IsAffineOpen U → U ≤ W →
      Function.Bijective (c.val.app (op (i ⁻¹ᵁ (U.ι ''ᵁ ⊤))))) : IsIso c := by
  let I := {U : X.affineOpens // U.1 ≤ W}
  let V : I → Y.Opens := fun u => i ⁻¹ᵁ (u.1.1.ι ''ᵁ ⊤)
  have hV : IsOpenCover V := by
    refine top_unique fun y _ => Opens.mem_iSup.2 ?_
    obtain ⟨U, hU, hyU, hUW⟩ :=
      exists_isAffineOpen_mem_and_subset (x := i y) (U := W) (hW ⟨y, rfl⟩)
    refine ⟨⟨⟨U, hU⟩, hUW⟩, ?_⟩
    show i y ∈ U.ι ''ᵁ ⊤
    rwa [Scheme.Opens.ι_image_top]
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict c V hV fun u => ?_
  have hVa : IsAffineOpen (V u) := by
    show IsAffineOpen (i ⁻¹ᵁ (u.1.1.ι ''ᵁ ⊤))
    rw [Scheme.Opens.ι_image_top]
    exact u.1.2.preimage i
  have : IsAffine (V u).toScheme := hVa
  have := isQuasicoherent_restrict M (V u)
  have := isQuasicoherent_restrict N (V u)
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  show Function.Bijective (c.val.app (op ((V u).ι ''ᵁ ⊤)))
  rw [Scheme.Opens.ι_image_top]
  exact h u.1.1 u.1.2 u.2

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- **The projections `A ⟶ Aₙ` are surjective**, the transitions of the system being surjective. -/
theorem surjective_limit_π (n : ℕ) : Function.Surjective (limit.π S.system (op n)).hom := by
  intro y
  obtain ⟨x, hx⟩ := invLimit.proj_surjective (fun k => S.system.obj (op k))
    (fun k => (S.system.map (homOfLE (Nat.le_succ k)).op).hom.toAddMonoidHom.toIntLinearMap)
    S.transition_surjective n y
  have hc := isLimitOfPreserves (forget CommRingCat) (limit.isLimit S.system)
  let s : (S.system ⋙ forget CommRingCat).sections := ⟨fun i => x.1 i.unop, by
    rintro ⟨i⟩ ⟨j⟩ g
    have hji : j ≤ i := leOfHom g.unop
    rw [show g = (homOfLE hji).op from Subsingleton.elim _ _]
    exact map_eq_of_map_succ_eq S.system x.1 x.2 hji⟩
  exact ⟨(Types.isLimitEquivSections hc).symm s,
    (Types.isLimitEquivSections_symm_apply hc s (op n)).trans hx⟩

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The affine edge isomorphism is natural**: `Hⁱ(RΓ(U, -)) = Γ(U, Hⁱ(-))` commutes with the
maps induced by a morphism of bounded below objects with quasi-coherent cohomology. -/
theorem homologySectionsOverIso_naturality (U : S.X.left.Opens) (hU : IsAffineOpen U)
    {E E' : DerivedCategory S.X.left.Modules} (φ : E ⟶ E') (n : ℤ) [E.IsGE n] [E'.IsGE n]
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj E).IsQuasicoherent)
    (hqc' : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj E').IsQuasicoherent)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).map ((S.sectionsOver U).map φ) ≫
        (S.homologySectionsOverIso U hU E' n hqc' i).hom =
      (S.homologySectionsOverIso U hU E n hqc i).hom ≫
        (globalSectionsOver (U.ι ≫ S.X.hom)).map ((Scheme.Modules.restrictFunctor U.ι).map
          ((DerivedCategory.homologyFunctor S.X.left.Modules i).map φ)) := by
  let edge := Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison
    (globalSectionsOver (U.ι ≫ S.X.hom)) (derivedGlobalSectionsOver (U.ι ≫ S.X.hom))
    (derivedGlobalSectionsOverUnit (U.ι ≫ S.X.hom))
    (Scheme.Modules.exists_quasiIso_isKInjective U) i
  let ψ := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map φ
  have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{u} ↑(limit S.system)) i).map
        ((derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).map ψ) ≫ edge.app _ =
      edge.app _ ≫ (globalSectionsOver (U.ι ≫ S.X.hom)).map
        ((DerivedCategory.homologyFunctor _ i).map ψ) :=
    edge.naturality ψ
  have h2 := ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso i).hom.naturality φ
  simp only [Functor.comp_map] at h2
  simp only [homologySectionsOverIso, affineEdgeIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Functor.comp_map]
  rw [← Category.assoc, h1]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

/-- **`Γ_A(U, (iₙ,* G)|_U) = Γ_{Aₙ}(Uₙ, G)` read over `A`**, for a quasi-coherent `𝒪_{Xₙ}`-module
`G`: the restriction to `U` of `iₙ,* G` is `(Uₙ ⟶ U)_*(G|_{Uₙ})`, whose `A`-linear global sections
are the `Aₙ`-linear global sections of `G|_{Uₙ}` by restriction of scalars. -/
def sectionsRestrictPushforwardIso (U : S.X.left.Opens) (n : ℕ)
    (G : (schemeAt S.system S.X n).Modules) [G.IsQuasicoherent] :
    (globalSectionsOver (U.ι ≫ S.X.hom)).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj
          ((Scheme.Modules.pushforward (S.closedImmersion n)).obj G)) ≅
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).obj
        ((globalSectionsOver ((S.levelOpen U n).ι ≫
          pullback.snd S.X.hom (baseProjection S.system n))).obj
          (G.restrict (S.levelOpen U n).ι)) :=
  haveI := S.closedSchemeProjection n
  (globalSectionsOver (U.ι ≫ S.X.hom)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
        restrictPushforwardIso (S.closedImmersion n) G U (S.levelOpen U n) rfl ≪≫
        (Scheme.Modules.pushforwardCongr (S.resLE_eq_levelOpenImmersion U n)).app _) ≪≫
    (pushforwardGlobalSectionsOverRestrictScalarsIso (S.levelOpenImmersion U n)
      (U.ι ≫ S.X.hom) ((S.levelOpen U n).ι ≫ pullback.snd S.X.hom (baseProjection S.system n))
      (limit.π S.system (op n)).hom (S.levelOpenImmersion_comp U n)).app _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The cohomology of the level-`n` term of the model system is quasi-coherent.** -/
theorem isQuasicoherent_homology_derivedPushforwardSystemOfModel (n : ℕ) (j : ℤ) :
    ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj
      (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).IsQuasicoherent := by
  by_cases hj : j = 0
  · subst hj
    exact (SheafOfModules.isQuasicoherent.{u} _).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (S.isQuasicoherent_pushforwardSystem_obj n)
  · exact (isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ (isFinitePresentation_of_isZero _
        (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hj))).1

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **In degree zero the level map is the zeroth level map**, read through the comparison of `H⁰`
with the embedding of modules into the derived category. -/
theorem homologyFunctor_map_levelMap (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ) :
    (DerivedCategory.homologyFunctor S.X.left.Modules 0).map (S.levelMap d p n) =
      S.zerothLevelMap d p n ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
        S.X.left.Modules 0).inv.app (S.pushforwardSystem.obj (op n)) :=
  (Iso.eq_comp_inv ((DerivedCategory.singleFunctorCompHomologyFunctorIso
    S.X.left.Modules 0).app (S.pushforwardSystem.obj (op n)))).2 rfl

/-- **Sections over an affine open of the unit `F ⟶ iₙ,* iₙ^* F` are surjective**, the projection
`A ⟶ Aₙ` being surjective. -/
theorem surjective_map_unit_app (U : S.X.left.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (F : S.X.left.Modules) [F.IsQuasicoherent] :
    Function.Surjective ((globalSectionsOver (U.ι ≫ S.X.hom)).map
      ((Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).unit.app F))) := by
  have := S.closedSchemeProjection n
  exact surjective_unit_app_of_isClosedImmersion (S.closedImmersion n) F _
    (by rwa [Scheme.Opens.ι_image_top])

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Part (3) of [Stacks, Tag 0CTH] over an affine open.** Let `U` be an affine open on which `K`
has cohomology only in degree zero, and suppose that the comparison of [Stacks, Tag 0CTG] at
level `n` over `U` is invertible. Then the canonical map `iₙ^* H⁰(K) ⟶ ℱₙ`, adjoint to the map
`H⁰(K) ⟶ iₙ,* ℱₙ`, is bijective on sections over `Uₙ`. In degree zero the comparison is
`Γ(U, H⁰(K)) ⊗_A Aₙ ⟶ Γ(Uₙ, ℱₙ)`, which factors through the surjection
`Γ(U, H⁰(K)) ⊗_A Aₙ ⟶ Γ(Uₙ, iₙ^* H⁰(K))`. -/
theorem bijective_app_levelAdjoint (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (U : S.X.left.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (hvan : ∀ j : ℤ, j ≠ 0 →
      IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict U.ι))
    (hG : IsIso (S.sectionsOverComparison d p U n)) :
    Function.Bijective
      ((((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
        (S.zerothLevelMap d p n)).val.app (op ((S.closedImmersion n) ⁻¹ᵁ (U.ι ''ᵁ ⊤)))) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)
  let F := (DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K
  have : F.IsQuasicoherent := d.quasicoherent 0
  have : d.K.IsGE 0 := d.isGE_zero_and_exists_isLE.1
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
    (S.closedImmersion n) F
  have := S.closedSchemeProjection n
  let c := (adj.homEquiv _ _).symm (S.zerothLevelMap d p n)
  let f := (limit.π S.system (op n)).hom
  let Γ := globalSectionsOver (U.ι ≫ S.X.hom)
  let R := Scheme.Modules.restrictFunctor U.ι
  let e1 := S.homologySectionsOverIso U hU d.K 0 d.quasicoherent 0
  let E2 := S.derivedPushforwardSystemOfModel.obj ⟨n⟩
  have hqc2 : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor S.X.left.Modules j).obj E2).IsQuasicoherent :=
    S.isQuasicoherent_homology_derivedPushforwardSystemOfModel n
  have : E2.IsGE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor S.X.left.Modules 0).obj (S.pushforwardSystem.obj (op n))).IsGE
        0)
  let e2 := S.homologySectionsOverIso U hU E2 0 hqc2 0
  let rsI := ((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso 0).app
    (S.levelSectionsOver U n)
  let ψ := Γ.map (R.map (adj.unit.app F))
  let ζ := Γ.map (R.map ((Scheme.Modules.pushforward (S.closedImmersion n)).map c))
  let σ := Γ.mapIso (R.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      S.X.left.Modules 0).app (S.pushforwardSystem.obj (op n))).symm) ≪≫ e2.symm ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso (S.sectionsOverPushforwardIso U n) ≪≫ rsI
  let τ := S.sectionsRestrictPushforwardIso U n
    ((Scheme.Modules.pullback (S.closedImmersion n)).obj F)
  -- the comparison in degree zero is `ψ ≫ ζ ≫ σ`
  have hz : adj.homEquiv _ _ c = S.zerothLevelMap d p n := Equiv.apply_symm_apply _ _
  have hnat := S.homologySectionsOverIso_naturality U hU (S.levelMap d p n) 0 d.quasicoherent
    hqc2 0
  have hrel : e1.inv ≫ (DerivedCategory.homologyFunctor _ 0).map (S.sectionsOverToLevel d p U n) ≫
      rsI.hom = ψ ≫ ζ ≫ σ.hom := by
    have h1 : e1.inv ≫ (DerivedCategory.homologyFunctor _ 0).map
        ((S.sectionsOver U).map (S.levelMap d p n)) =
        Γ.map (R.map ((DerivedCategory.homologyFunctor S.X.left.Modules 0).map
          (S.levelMap d p n))) ≫ e2.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    simp only [sectionsOverToLevel, Functor.map_comp, ← Category.assoc]
    rw [h1, S.homologyFunctor_map_levelMap d p n, ← hz, Adjunction.homEquiv_unit]
    simp only [σ, ψ, ζ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
    rfl
  have hθ : IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
      (ψ ≫ ζ ≫ σ.hom)) := by
    have hc := StacksDraft.TopDegreeExtendScalars.topDegreeComparison_comp f
      (S.sectionsOverToLevel d p U n) 0
    rw [← hrel, Adjunction.homEquiv_naturality_left_symm]
    show IsIso (_ ≫ ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
      (_ ≫ ((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso 0).hom.app _))
    rw [← hc]
    have := S.isLE_sectionsOver d U hU 0 fun i hi => hvan i (by omega)
    have := StacksDraft.TopDegreeExtendScalars.isIso_topDegreeComparison f
      ((S.sectionsOver U).obj d.K) 0
    have : IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison f
      (S.sectionsOverToLevel d p U n)) := hG
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective ζ).1 (isIso_of_isIso_homEquiv_symm_comp f
    (S.surjective_limit_π n) ψ (S.surjective_map_unit_app U hU n F) ζ σ τ hθ)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTH] from [Stacks, Tag 0CTF] and [Stacks, Tag 0CTG].** Granted that `K` is
pseudo-coherent relative to `A` and that the comparison maps `RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` are
invertible over affine opens `U`, there is an open `W ⊇ X₀` such that

1. `Hⁱ(K)|_W = 0` for `i ≠ 0`;
2. `H⁰(K)|_W` is of finite presentation;
3. the canonical maps `iₙ^* H⁰(K) ⟶ ℱₙ` are isomorphisms.

The canonical maps are adjoint to the maps `H⁰(K) ⟶ iₙ,* ℱₙ` induced by `K ⟶ L ⟶ iₙ,* ℱₙ`. -/
theorem exists_open_of_isPseudoCoherent_of_isIso_sectionsOverComparison
    (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hpc : S.X.hom.IsPseudoCoherent d.K)
    (hG : ∀ U : S.X.left.Opens, IsAffineOpen U → ∀ n : ℕ,
      IsIso (S.sectionsOverComparison d p U n)) :
    ∃ W : S.X.left.Opens, Set.range (S.closedImmersion 0) ⊆ W ∧
      (∀ j : ℤ, j ≠ 0 →
        IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict W.ι)) ∧
      (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).restrict
        W.ι).IsFinitePresentation ∧
      ∀ n : ℕ, IsIso
        (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
          (S.zerothLevelMap d p n)) := by
  obtain ⟨W, hW, hvan, hfp⟩ := S.exists_open_isZero_homology_restrict_and_isFinitePresentation
    d p hpc fun U hU => hG U hU 0
  refine ⟨W, hW, hvan, hfp, fun n => ?_⟩
  have := S.closedSchemeProjection n
  have : ((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).IsQuasicoherent :=
    d.quasicoherent 0
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
    (S.closedImmersion n) ((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K)
  have : (S.F n).IsQuasicoherent :=
    (isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ (S.finitelyPresented n)).1
  exact isIso_of_bijective_app_preimage (S.closedImmersion n) _ W
    ((S.range_closedImmersion_eq n).trans_subset hW) fun U hU hUW =>
      S.bijective_app_levelAdjoint d p U hU n
        (fun j hj => isZero_restrict_of_le _ hUW (hvan j hj)) (hG U hU n)

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
