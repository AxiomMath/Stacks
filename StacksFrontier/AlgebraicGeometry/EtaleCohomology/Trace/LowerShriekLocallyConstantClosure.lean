module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyConstantUnibranch
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf

/-!
# Local constancy of the `Rˢ g_!` along extensions and direct summands

Let `g : U ⟶ W` be separated of finite type with a compactification. The sheaves `A` of
`ℤ_ℓ`-modules on `U` all of whose `Rˢ g_! A` are locally constant of finite type are closed under
isomorphisms, direct summands (`Rˢ g_!` preserves retracts, and a retract is a kernel) and
extensions (the long exact sequence of `R g_!` and Tag 093U (3)). So they contain the closure
`Stacks.EtaleCohomology.IsExtensionSummandClosure S` of any class `S` of such sheaves
(`Stacks.EtaleCohomology.forall_isFiniteTypeLocallyConstant_lowerShriekHomology_of_closure`).

Together with the generic local constancy of the `Rˢ g_!` of finitely many constructible torsion
sheaves over a nonempty basic open (Tag 0GL0, now a theorem,
`Stacks.EtaleCohomology.lowerShriekConstructibilityInput`), stable under every base change
`V' ⟶ D(f)` (Tag 0F7L,
`Stacks.EtaleCohomology.exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology`),
this lets one compare `Rʳ g_! G` for two ℓ-adic sheaves `G` whose lattices differ: lisseness of
`Rʳ g_! G` only depends on the level zero of the flat model of `G`
(`Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero`), and it is
enough that this level zero be an iterated extension of direct summands of sheaves whose `Rˢ g_!`
are locally constant. This is how the lattice of a constant field extension of a family is
handled in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Laumon's Fourier family).

## Main definitions

* `Stacks.EtaleCohomology.IsExtensionSummandClosure`: the closure of a class of objects of an
  abelian category under isomorphisms, retracts and extensions.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero`.
* `Stacks.EtaleCohomology.forall_isFiniteTypeLocallyConstant_lowerShriekHomology_of_closure`.
* `Stacks.EtaleCohomology.exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

/-! ### The closure under extensions and summands -/

section Closure

variable {C : Type*} [Category* C] [Abelian C]

/-- **The closure of a class `S` under isomorphisms, retracts and extensions**: the smallest
class containing `S`, closed under isomorphisms, containing every retract of its members, and
containing the middle term of every short exact sequence whose outer terms lie in it. -/
inductive IsExtensionSummandClosure (S : ObjectProperty C) : ObjectProperty C
  | of_mem {A : C} : S A → IsExtensionSummandClosure S A
  | of_iso {A A' : C} (e : A ≅ A') : IsExtensionSummandClosure S A → IsExtensionSummandClosure S A'
  | of_retract {A B : C} (i : A ⟶ B) (r : B ⟶ A) (h : i ≫ r = 𝟙 A) :
      IsExtensionSummandClosure S B → IsExtensionSummandClosure S A
  | of_shortExact {T : ShortComplex C} (hT : T.ShortExact) :
      IsExtensionSummandClosure S T.X₁ → IsExtensionSummandClosure S T.X₃ →
        IsExtensionSummandClosure S T.X₂

/-- **The closure is the smallest such class**: a class containing `S` and closed under
isomorphisms, retracts and extensions contains `IsExtensionSummandClosure S`. -/
theorem IsExtensionSummandClosure.le {S P : ObjectProperty C} (hS : ∀ A, S A → P A)
    (hiso : ∀ {A A' : C}, (A ≅ A') → P A → P A')
    (hret : ∀ {A B : C} (i : A ⟶ B) (r : B ⟶ A), i ≫ r = 𝟙 A → P B → P A)
    (hext : ∀ {T : ShortComplex C}, T.ShortExact → P T.X₁ → P T.X₃ → P T.X₂) {A : C}
    (hA : IsExtensionSummandClosure S A) : P A := by
  induction hA with
  | of_mem h => exact hS _ h
  | of_iso e _ ih => exact hiso e ih
  | of_retract i r h _ ih => exact hret i r h ih
  | of_shortExact hT _ _ ih₁ ih₃ => exact hext hT ih₁ ih₃

/-- **An exact functor carries the closure into the closure**: if `F` preserves finite limits and
colimits and carries `S` into `IsExtensionSummandClosure S'`, it carries
`IsExtensionSummandClosure S` into `IsExtensionSummandClosure S'`. -/
theorem IsExtensionSummandClosure.map {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {S : ObjectProperty C}
    {S' : ObjectProperty D} (hS : ∀ A, S A → IsExtensionSummandClosure S' (F.obj A)) {A : C}
    (hA : IsExtensionSummandClosure S A) : IsExtensionSummandClosure S' (F.obj A) :=
  IsExtensionSummandClosure.le (P := fun A => IsExtensionSummandClosure S' (F.obj A)) hS
    (fun e h => .of_iso (F.mapIso e) h) (fun i r h hB => .of_retract (F.map i) (F.map r)
      (by rw [← F.map_comp, h, CategoryTheory.Functor.map_id]) hB)
    (fun {T} hT h₁ h₃ => .of_shortExact (T := T.map F) (hT.map_of_exact F) h₁ h₃) hA

/-- **A retract is a kernel**: `i : A ⟶ B` with retraction `r` is a kernel of `𝟙 - r ≫ i`. -/
def isLimitRetractKernelFork {A B : C} (i : A ⟶ B) (r : B ⟶ A) (h : i ≫ r = 𝟙 A) :
    IsLimit (KernelFork.ofι (f := 𝟙 B - r ≫ i) i
      (by rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, h, Category.id_comp,
        sub_self])) :=
  KernelFork.IsLimit.ofι _ _ (fun k _ => k ≫ r)
    (fun k hk => by
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hk
      rw [Category.assoc, ← hk])
    (fun k hk m hm => by rw [← hm, Category.assoc, h, Category.comp_id])

/-- **A weak Serre class is closed under retracts**. -/
theorem prop_of_retract (P : ObjectProperty C) [P.IsWeakSerreClass] {A B : C} (i : A ⟶ B)
    (r : B ⟶ A) (h : i ≫ r = 𝟙 A) (hB : P B) : P A :=
  P.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel (𝟙 B - r ≫ i))
    (isLimitRetractKernelFork i r h)) (P.prop_kernel _ hB hB)

end Closure

/-! ### `Rˢ g_!` along the closure -/

section LowerShriek

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ]

/-- **Local constancy of all the `Rˢ f_!` along the closure**: if every `Rˢ f_! A` lies in a weak
Serre class `P` for every `A` of `S`, then so does every `Rˢ f_! A` for `A` in
`IsExtensionSummandClosure S`. -/
theorem forall_prop_lowerShriekHomology_of_closure
    (P : ObjectProperty (EtaleModules.{u, 0} Λ Y)) [P.IsWeakSerreClass]
    {S : ObjectProperty (EtaleModules.{u, 0} Λ X)}
    (hS : ∀ A, S A → ∀ s : ℤ, P ((lowerShriekHomology Λ f j s).obj A))
    {A : EtaleModules.{u, 0} Λ X} (hA : IsExtensionSummandClosure S A) (s : ℤ) :
    P ((lowerShriekHomology Λ f j s).obj A) :=
  IsExtensionSummandClosure.le
    (P := fun A => ∀ s : ℤ, P ((lowerShriekHomology Λ f j s).obj A)) hS
    (fun e h s => P.prop_of_iso ((lowerShriekHomology Λ f j s).mapIso e) (h s))
    (fun i r h hB s => prop_of_retract P ((lowerShriekHomology Λ f j s).map i)
      ((lowerShriekHomology Λ f j s).map r)
      (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])
      (hB s))
    (fun hT h₁ h₃ s => prop_homology_derivedLowerShriek_singleFunctor_of_shortExact f j Λ P _ hT
      h₁ h₃ s) hA s

/-- **Local constancy of finite type of all the `Rˢ f_!` along the closure.** -/
theorem forall_isFiniteTypeLocallyConstant_lowerShriekHomology_of_closure [IsNoetherianRing Λ]
    {S : ObjectProperty (EtaleModules.{u, 0} Λ X)}
    (hS : ∀ A, S A → ∀ s : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ
      Y.smallEtaleTopology ((lowerShriekHomology Λ f j s).obj A))
    {A : EtaleModules.{u, 0} Λ X} (hA : IsExtensionSummandClosure S A) (s : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ Y.smallEtaleTopology
      ((lowerShriekHomology Λ f j s).obj A) :=
  forall_prop_lowerShriekHomology_of_closure f j Λ
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      Y.smallEtaleTopology Λ) hS hA s

end LowerShriek

/-! ### Lisseness of `Rʳ g_! G` from the level zero -/

section LevelZero

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)]
  (jg : CompactificationOf (Over.mk (B.inclusion.map g)))

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] in
/-- **`Rʳ g_! G` is lisse as soon as the `Rˢ g_!` of the level zero of its flat model are locally
constant of finite type**: by dévissage every `Rʳ g_! G'ₘ` is then locally constant of finite
type (`Stacks.EtaleCohomology.LAdicSheaf.isFiniteTypeLocallyConstant_lowerShriekTower`), and so
are the levels of `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek`). -/
theorem LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero (G : LAdicSheaf B U ℓ)
    (h0 : ∀ s : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
      W.1.smallEtaleTopology ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg s).obj
        (towerObj (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G)) 0)))
    (r : ℕ) : (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r).IsLisse :=
  LAdicSheaf.isLisse_higherDirectImageShriek B ℓ g jg G r
    (LAdicSheaf.isFiniteTypeLocallyConstant_lowerShriekTower B ℓ g jg G h0 r)

/-- **The level zero of the flat model of `G|_{U'}` is the restriction of that of `G`.** -/
def LAdicSheaf.flatModelLevelZeroInverseImageIso {U' : B.Scheme} [IsNoetherian U'.1]
    (jU : U' ⟶ U) (G : LAdicSheaf B U ℓ) :
    towerObj (LAdicSheaf.padicTower B U' ℓ
      (LAdicSheaf.flatModel B ℓ (SmallEtale.LAdicSheaf.inverseImage jU G))) 0 ≅
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj
        (towerObj (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G)) 0) :=
  LAdicSheaf.padicTowerObjIsoOfLevelIso 0 (LAdicSheaf.flatModelInverseImageLevelZeroIso jU G) ≪≫
    ((LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ G)).app (op 0)).symm

end LevelZero

/-! ### Generic local constancy of the `Rˢ g_!` of finitely many torsion sheaves -/

section GenericLocus

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (hR : schemeSizeBelow B.cutoff (Spec (.of R)))

/-- **`Rˢ f_! Q` is the `s`-th homology of `Rf_!` applied to `Q` placed in degree `0`.** -/
def lowerShriekHomologyIsoHomologyDerivedLowerShriek (Λ : Type) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) (Q : EtaleModules.{u, 0} Λ X) (s : ℤ) :
    (lowerShriekHomology Λ f j s).obj Q ≅ (DerivedCategory.Plus.homologyFunctor _ s).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj Q)) :=
  (DerivedCategory.Plus.homologyFunctor _ s).mapIso ((derivedLowerShriek.{u, 0} f j Λ).mapIso
    ((StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ X)).app Q))

/-- **`Rˢ f_!` of a sheaf killed by some `m > 0` vanishes outside `[0, N]`**, for one `N` depending
only on `f` and its compactification (Tag 0G2A). -/
theorem exists_isZero_lowerShriekHomology_of_nsmul_id_eq_zero (Λ : Type) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) [CompactSpace Y] :
    ∃ N : ℕ, ∀ (Q : EtaleModules.{u, 0} Λ X) (m : ℕ), 0 < m → m • 𝟙 Q = 0 →
      ∀ s : ℤ, s < 0 ∨ (N : ℤ) < s → IsZero ((lowerShriekHomology Λ f j s).obj Q) := by
  obtain ⟨N, hN, -⟩ := exists_bounded_derivedLowerShriek Λ f j
  refine ⟨N, fun Q m hm hQ s hs => ?_⟩
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0
  let Φ := derivedLowerShriek.{u, 0} f j Λ
  have hSQ : m • 𝟙 (S.obj Q) = 0 := by
    rw [← S.map_id, ← Functor.map_nsmul, hQ, Functor.map_zero]
  obtain ⟨-, -, hGE, hLE⟩ := hN (S.obj Q) (isTorsionPlus_of_nsmul_id_eq_zero _ _ hm hSQ)
  refine IsZero.of_iso ?_ (lowerShriekHomologyIsoHomologyDerivedLowerShriek Λ f j Q s)
  rcases hs with hs | hs
  · have := hGE 0 (inferInstanceAs ((S.obj Q).IsGE 0))
    exact DerivedCategory.isZero_of_isGE (DerivedCategory.Plus.ι.obj (Φ.obj (S.obj Q))) 0 s hs
  · have := hLE 0 (inferInstanceAs ((S.obj Q).IsLE 0))
    exact DerivedCategory.isZero_of_isLE (DerivedCategory.Plus.ι.obj (Φ.obj (S.obj Q)))
      (0 + N) s (by omega)

/-- **Inverse images along `V' ⟶ V ⟶ W` of a family vanishing outside `[0, N]` and locally
constant on `V` inside `[0, N]` are locally constant of finite type.** -/
theorem isFiniteTypeLocallyConstant_etaleModuleInverseImage_comp_of_bounded {Λ : Type} [Ring Λ]
    {V' V W : B.Scheme} (jV' : V' ⟶ V) (o : V ⟶ W) (P : ℤ → EtaleModules.{u, 0} Λ W.1) (N : ℕ)
    (hZ : ∀ s : ℤ, s < 0 ∨ (N : ℤ) < s → IsZero (P s))
    (hlc : ∀ n : ℕ, n ≤ N → Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B V.1 V.property)
      (((AlgebraicGeometry.smallEtaleBaseChange B o).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B W.1 W.property) (SmallEtale.topology B V.1 V.property)).obj
          ((etaleModulesToSmallEtale B W Λ).obj (P n)))) (s : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ V'.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (jV' ≫ o))).obj (P s)) := by
  by_cases hs : s < 0 ∨ (N : ℤ) < s
  · have := (etaleModuleInverseImageAdj.{u, 0} Λ (B.inclusion.map (jV' ≫ o))).isLeftAdjoint
    have : (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (jV' ≫ o))).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isLeftAdjoint _
    exact ObjectProperty.prop_of_isZero
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
        V'.1.smallEtaleTopology Λ) (Functor.map_isZero _ (hZ s hs))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
    exact isFiniteTypeLocallyConstant_etaleModuleInverseImage_comp jV' o (P n) (hlc n (by omega))

/-- A Noetherian scheme is compact and quasi-separated. -/
private theorem compactSpace_and_quasiSeparatedSpace_of_isNoetherian {X : Scheme}
    (h : IsNoetherian X) : CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨h.toCompactSpace, @IsLocallyNoetherian.quasiSeparatedSpace _ h.toIsLocallyNoetherian⟩

/-- **A basic open over which the `Rˢ g_!` of finitely many constructible torsion sheaves are
locally constant, after any base change**: for `g : U ⟶ Spec R` separated of finite type (`R` a
Noetherian domain) and finitely many constructible sheaves `Qᵢ` of `ℤ_ℓ`-modules on `U` killed by
`m > 0`, there is `f ≠ 0` in `R` such that for every Noetherian `V'` with a morphism
`jV' : V' ⟶ Spec R` landing in `D(f)`, every cartesian square `U' = U ×_{Spec R} V'` and every
compactification of `g' : U' ⟶ V'`, all the `Rˢ g'_!(Qᵢ|_{U'})` are locally constant of finite
type. Generic local constancy of the finitely many nonzero `Rˢ g_! Qᵢ` (Tag 0GL0 and Tag 0G2A),
then proper base change (Tag 0F7L). -/
theorem exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology {ℓ : ℕ}
    [Fact ℓ.Prime]
    {U : B.Scheme} [IsNoetherian U.1] (g : U ⟶ Stacks.ArtinSchreier.specObject R B hR)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] {ι : Type} [Finite ι]
    (Q : ι → EtaleModules.{u, 0} ℤ_[ℓ] U.1)
    (hQc : ∀ i, IsBigSiteConstructibleEtaleModule B U ℤ_[ℓ] (Q i)) (m : ℕ) (hm : 0 < m)
    (hQ : ∀ i, m • 𝟙 (Q i) = 0) :
    ∃ f : R, f ≠ 0 ∧ ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject R B hR) (jU : U' ⟶ U) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')]
      (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
      Set.range (B.inclusion.map jV') ⊆ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
        (B.inclusion.map jV') →
      ∀ (i : ι) (s : ℤ), Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
        V'.1.smallEtaleTopology ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).obj
          ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj (Q i))) := by
  classical
  have := Fintype.ofFinite ι
  let W := Stacks.ArtinSchreier.specObject R B hR
  have : IsReduced W.1 := inferInstanceAs (IsReduced (Spec (.of R)))
  have hNW' : IsNoetherian W.1 := inferInstanceAs (IsNoetherian (Spec (.of R)))
  have : Nonempty W.1 := inferInstanceAs (Nonempty (PrimeSpectrum R))
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isNoetherian
    (show IsNoetherian (B.inclusion.obj W) from hNW')
  obtain ⟨jg, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace (B.inclusion.map g)
  let P : ι → ℤ → EtaleModules.{u, 0} ℤ_[ℓ] W.1 := fun i s =>
    (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg s).obj (Q i)
  have hQt : ∀ i, IsTorsionEtaleModule ℤ_[ℓ] U.1 (Q i) := fun i =>
    isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero (Q i) _ hm (hQ i)
  have hPc : ∀ i s, IsBigSiteConstructibleEtaleModule B W ℤ_[ℓ] (P i s) := fun i s =>
    IsBigSiteConstructibleEtaleModule.of_iso B ℤ_[ℓ]
      (lowerShriekHomologyIsoHomologyDerivedLowerShriek ℤ_[ℓ] _ jg (Q i) s).symm
      (lowerShriekConstructibilityInput B (B.inclusion.map g) jg ℤ_[ℓ] (Q i) (hQc i) (hQt i) s)
  obtain ⟨N, hZ⟩ :=
    exists_isZero_lowerShriekHomology_of_nsmul_id_eq_zero ℤ_[ℓ] (B.inclusion.map g) jg
  obtain ⟨V, o, ho, ⟨v⟩, hlc⟩ := exists_isOpenImmersion_forall_isFiniteTypeLocallyConstant B
    ℤ_[ℓ] (Finset.univ ×ˢ Finset.range (N + 1)) W
    (fun p : ι × ℕ => (etaleModulesToSmallEtale B W ℤ_[ℓ]).obj (P p.1 p.2))
    (fun p _ => hPc p.1 p.2)
  -- a basic open `D(f)` inside the image of `V`
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hvf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (⟨v, rfl⟩ : ((B.inclusion.map o) v : PrimeSpectrum R) ∈ Set.range (B.inclusion.map o))
      (B.inclusion.map o).isOpenEmbedding.isOpen_range
  refine ⟨f, fun h => hvf (h ▸ Ideal.zero_mem _),
    fun V' U' _ _ jV' jU g' _ _ _ jg' hrange hpb i s => ?_⟩
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_isNoetherian
    (show IsNoetherian (B.inclusion.obj V') from ‹IsNoetherian V'.1›)
  let jV'' : V' ⟶ V := ObjectProperty.homMk
    (IsOpenImmersion.lift (B.inclusion.map o) (B.inclusion.map jV') (hrange.trans hf))
  have hfac : jV'' ≫ o = jV' := by
    ext : 1
    exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e⟩ := nonempty_lowerShriekHomology_inverseImage_iso ℤ_[ℓ] hpb jg jg' (Q i) m hm (hQ i) s
  refine ObjectProperty.prop_of_iso
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      V'.1.smallEtaleTopology ℤ_[ℓ]) e.symm ?_
  rw [← hfac]
  exact isFiniteTypeLocallyConstant_etaleModuleInverseImage_comp_of_bounded B jV'' o (P i) N
    (hZ (Q i) m hm (hQ i)) (fun n hn => hlc (i, n)
      (Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_range.2 (by omega)⟩)) s

end GenericLocus

end Stacks.EtaleCohomology
