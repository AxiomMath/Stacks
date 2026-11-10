module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedTensorProduct
public import StacksFrontier.Topology.Sheaves.Modules.StalkKFlat
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RegularPerfect
import StacksFrontier.Homology.KFlat.AcyclicModule
import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion

/-!
# Coherence and support of the Tor sheaves

Let `X` be a locally Noetherian scheme. The Tor sheaves
`Tor_p^{𝒪_X}(ℱ, 𝒢) = H^{-p}(ℱ ⊗ᴸ_{𝒪_X} 𝒢)` of two coherent `𝒪_X`-modules are coherent, and
`D⁻_Coh(𝒪_X)` — the complexes which are bounded above and have coherent cohomology sheaves — is
closed under the derived tensor product.

On an arbitrary scheme every `Tor_p^{𝒪_X}(ℱ, 𝒢)` is supported on `Supp(ℱ) ∩ Supp(𝒢)`, and on a
regular — that is, nonsingular — scheme the Tor sheaves of two coherent modules are coherent,
regularity entering only through local Noetherianity. These are two of the four clauses of
[Stacks, Tag 0AZT]; the other two, that the stalk of `Tor_p^{𝒪_X}(ℱ, 𝒢)` at `x` is
`Tor_p^{𝒪_{X, x}}(ℱ_x, 𝒢_x)` and that the Tor sheaves vanish for `p > dim(X)`, are not proved
here.

Part (2) is proved first, from the identification of the pseudo-coherent objects of
`D_QCoh(𝒪_X)` with `D⁻_Coh(𝒪_X)` ([Stacks, Tag 08E8]) and the stability of pseudo-coherence
under the derived tensor product ([Stacks, Tag 09J3]); the quasi-coherence of the cohomology of
the derived tensor product, which the first of these needs as an input, is [Stacks, Tag 08DX].
Part (1) is part (2) applied to the two modules placed in degree `0`: such an object is bounded
above and its only nonzero cohomology sheaf is the module itself.

The support statement is proved stalkwise. Taking stalks at `x` is exact, so it commutes with
cohomology and carries a total tensor complex to the total tensor complex of the two complexes
of stalks ([Stacks, Tag 01CB] read at the level of complexes); writing `ℱ` and `𝒢` as the
classes of K-flat complexes `P` and `Q` therefore presents the stalk of `Tor_p^{𝒪_X}(ℱ, 𝒢)` at
`x` as `H^{-p}(Tot(P_x ⊗_{𝒪_{X, x}} Q_x))`. If the stalk of `ℱ` at `x` vanishes then `P_x` is
acyclic, and `Tot(P_x ⊗ Q_x)` is acyclic because `Q_x` is K-flat ([Stacks, Tag 06YB]); if the
stalk of `𝒢` vanishes the same argument runs with the two roles exchanged, K-flatness over a
commutative ring being a condition on either variable of the tensor product. This gives no
identification of the stalk with a Tor module over `𝒪_{X, x}`, which is why the stalk clause of
[Stacks, Tag 0AZT] is absent, and with it the degree bound that is deduced from it.

## Main definitions

* `AlgebraicGeometry.TorFormula.derivedTensor`: `⊗ᴸ_{𝒪_X}` on `D(𝒪_X)` for a scheme `X`.
* `AlgebraicGeometry.TorFormula.torSheaf`: the Tor sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)`.
* `AlgebraicGeometry.TorFormula.stalkTorSheafIso`: the stalk of a Tor sheaf as the cohomology of
  the total tensor complex of two complexes of stalks.

## Main results

* `AlgebraicGeometry.TorFormula.isCoherent_torSheaf`: part (1), the Tor sheaves of two coherent
  modules on a locally Noetherian scheme are coherent.
* `AlgebraicGeometry.TorFormula.derivedCategoryBMinus_derivedTensor`: part (2), `D⁻_Coh(𝒪_X)` is
  closed under the derived tensor product.
* `AlgebraicGeometry.TorFormula.supp_torSheaf_subset_inter`: the Tor sheaves are supported on
  the intersection of the supports of the two modules.
* `AlgebraicGeometry.TorFormula.isCoherent_torSheaf_of_isRegular`: on a regular scheme the Tor
  sheaves of two coherent modules are coherent.

## Implementation notes

`D⁻_Coh(𝒪_X)` is `DerivedCategoryB.derivedCategoryBMinus` at the coherence property, that is,
the conjunction of `DerivedCategoryB.IsBoundedAbove` and coherence of every cohomology sheaf.

*Two models of `D(𝒪_X)`.* Pseudo-coherence on a ringed space is developed at the standard model
`CategoryTheory.HasDerivedCategory.standard`, which the statements of [Stacks, Tag 08E8] and
[Stacks, Tag 09J3] therefore mention, while [Stacks, Tag 08DX] is available only at the locally
small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, because essential
surjectivity of derived sheafification is. The two are different types and no comparison functor
between them is used here. Instead the quasi-coherence statement is crossed at the level of
*complexes*, where there is no derived category to disagree about:
`isQuasicoherent_homology_totalTensorComplex` is a statement about the total tensor complex of
two K-flat complexes, proved at the locally small model, and
`isQuasicoherent_homology_derivedTensor` reads it back at the standard model through K-flat
representatives, the derived tensor product being the total tensor complex on those. Everything
after that lemma is at the standard model, which the local instance of raised priority selects
in preference to the locally small one.

## References

* [Stacks Project, Tag 0AZS](https://stacks.math.columbia.edu/tag/0AZS)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 09J3](https://stacks.math.columbia.edu/tag/09J3)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.TorFormula

/-! ### Quasi-coherence of the cohomology of a total tensor complex -/

/-- The cohomology of a complex is quasi-coherent iff that of its class in `D(𝒪_X)` is. -/
private theorem isQuasicoherent_homology_Q_obj_iff.{w} (X : Scheme.{u})
    [HasDerivedCategory.{w} X.Modules]
    (A : Stacks.Duality.TensorComplex X) (j : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules j).obj (DerivedCategory.Q.obj A)).IsQuasicoherent ↔
      (A.homology j).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_iff_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules j).app A)

/-- **The cohomology sheaves of the total tensor complex of two K-flat complexes with
quasi-coherent cohomology are quasi-coherent.** This is [Stacks, Tag 08DX] part (1) read at the
level of complexes: `Tot(P ⊗_{𝒪_X} Q)` represents the derived tensor product of the classes of
`P` and of `Q`, and the cohomology of the class of a complex is the cohomology of the complex. -/
theorem isQuasicoherent_homology_totalTensorComplex (X : Scheme.{u})
    (P Q : Stacks.Duality.TensorComplex X)
    (hP : Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf P)
    (hQ : Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf Q)
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherent)
    (hQq : ∀ j : ℤ, (Q.homology j).IsQuasicoherent)
    (i : ℤ) :
    ((Stacks.Duality.totalTensorComplex P Q).homology i).IsQuasicoherent := by
  have h1 : ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex P Q))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules i).mapIso
        ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparison P Q hP hQ))
      (Stacks.Duality.isQuasicoherent_homology_derivedTensor X
        ⟨DerivedCategory.Q.obj P, fun j => (isQuasicoherent_homology_Q_obj_iff X P j).2 (hPq j)⟩
        ⟨DerivedCategory.Q.obj Q, fun j => (isQuasicoherent_homology_Q_obj_iff X Q j).2 (hQq j)⟩
        i)
  exact (isQuasicoherent_homology_Q_obj_iff X _ i).1 h1

section

-- The priority selects the standard model of `D(𝒪_X)`, which pseudo-coherence is developed at,
-- over the locally small one supplied by `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.
attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The derived tensor product and the Tor sheaves -/

/-- **`⊗ᴸ_{𝒪_X}`, the derived tensor product on `D(𝒪_X)` for a scheme `X`.** A scheme is a ringed
space and a ringed space is the ringed site of its opens, so this is the derived tensor product
of [Stacks, Tag 06YH]. -/
abbrev derivedTensor (X : Scheme.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor

/-- **The Tor sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)`**: the `(-p)`-th cohomology sheaf of the derived tensor
product of `ℱ` and `𝒢`, each placed in degree `0`. -/
def torSheaf (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules (-(p : ℤ))).obj
    (((derivedTensor X).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj G))

/-! ### Quasi-coherence of the cohomology of the derived tensor product -/

/-- **Every object of `D(𝒪_X)` is the class of a K-flat complex**, by the existence of K-flat
resolutions ([Stacks, Tag 06YS]) and the invertibility of a quasi-isomorphism in the derived
category. -/
theorem exists_kFlatComplex_iso (X : Scheme.{u}) (E : DerivedCategory X.Modules) :
    ∃ P : Stacks.Duality.TensorComplex X, Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf P ∧
      Nonempty ((DerivedCategory.Q.obj P : DerivedCategory X.Modules) ≅ E) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.sheaf
    (DerivedCategory.Q.objPreimage E)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := Stacks.DerivedTensor.RingedSite.Modules X.sheaf) p).2 hp
  exact ⟨P, hP, ⟨@asIso _ _ _ _ (DerivedCategory.Q.map p) hiso ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- **[Stacks, Tag 08DX] part (1): the cohomology sheaves of `K ⊗ᴸ_{𝒪_X} L` are quasi-coherent
as soon as those of `K` and of `L` are.** Each factor is replaced by a K-flat representative, on
which the derived tensor product is the total tensor complex. -/
theorem isQuasicoherent_homology_derivedTensor (X : Scheme.{u})
    (K L : DerivedCategory X.Modules)
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent)
    (hL : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj L).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derivedTensor X).obj K).obj L)).IsQuasicoherent := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_kFlatComplex_iso X K
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_kFlatComplex_iso X L
  have hAq : ∀ j : ℤ, (A.homology j).IsQuasicoherent := fun j =>
    (isQuasicoherent_homology_Q_obj_iff X A j).1
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules j).mapIso eA).symm (hK j))
  have hBq : ∀ j : ℤ, (B.homology j).IsQuasicoherent := fun j =>
    (isQuasicoherent_homology_Q_obj_iff X B j).1
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules j).mapIso eB).symm (hL j))
  have eG : (DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex A B) :
      DerivedCategory X.Modules) ≅ ((derivedTensor X).obj K).obj L :=
    ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparison A B hA hB).symm ≪≫
      ((derivedTensor X).mapIso eA).app _ ≪≫ ((derivedTensor X).obj K).mapIso eB
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules i).mapIso eG)
    ((isQuasicoherent_homology_Q_obj_iff X _ i).2
      (isQuasicoherent_homology_totalTensorComplex X A B hA hB hAq hBq i))

/-! ### `D⁻_Coh(𝒪_X)` is closed under the derived tensor product -/

/-- **An object of `D⁻_Coh(𝒪_X)` is pseudo-coherent.** This is the easy half of
[Stacks, Tag 08E8] at a locally Noetherian scheme: a coherent module placed in a single degree
is pseudo-coherent in every degree, and an object bounded above whose cohomology sheaves are
pseudo-coherent in the shifted degrees is pseudo-coherent. -/
theorem isPseudoCoherent_of_isBoundedAbove_of_isCoherent_homology (X : Scheme.{u})
    [IsLocallyNoetherian X] (E : DerivedCategory X.Modules)
    (hb : DerivedCategoryB.IsBoundedAbove E)
    (hc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E := by
  obtain ⟨b, hbz⟩ := hb
  have hfrom : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m := fun m =>
    RingedSpace.isPseudoCoherentFrom_of_isLE_homology E m b
      ((DerivedCategory.isLE_iff E b).mpr fun j hj => hbz j hj)
      fun i _ => isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent X _
        (hc i).stacksIsCoherent (m - i)
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := DerivedCategory.Q (C := StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) E
  exact ⟨K, fun m => RingedSpace.isPseudoCoherentComplexFrom_of_iso E m (hfrom m) K e, ⟨e⟩⟩

/-- **[Stacks, Tag 0AZS] part (2).** Let `X` be a locally Noetherian scheme. If `K` and `L` are
in `D⁻_Coh(𝒪_X)` then so is `K ⊗ᴸ_{𝒪_X} L`.

Being in `D⁻_Coh(𝒪_X)` is equivalent to being pseudo-coherent ([Stacks, Tag 08E8]), and the
derived tensor product of two pseudo-coherent objects is pseudo-coherent
([Stacks, Tag 09J3]). Reading the equivalence backwards needs the cohomology sheaves of the
derived tensor product to be quasi-coherent, which is [Stacks, Tag 08DX]; the bound above is
`a + b` for bounds `a` and `b` of the two factors. -/
@[stacks 0AZS "part (2): D⁻_Coh is closed under the derived tensor product",
  sga "6 I 2.16.1" "b), special case"]
theorem derivedCategoryBMinus_derivedTensor (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K L : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryBMinus (fun F : X.Modules => F.IsCoherent) K)
    (hL : DerivedCategoryB.derivedCategoryBMinus (fun F : X.Modules => F.IsCoherent) L) :
    DerivedCategoryB.derivedCategoryBMinus (fun F : X.Modules => F.IsCoherent)
      (((derivedTensor X).obj K).obj L) := by
  obtain ⟨hKb, hKc⟩ := hK
  obtain ⟨hLb, hLc⟩ := hL
  have hKq : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent :=
    fun j => have := hKc j; _root_.isQuasicoherent_of_isCoherent _
  have hLq : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj L).IsQuasicoherent :=
    fun j => have := hLc j; _root_.isQuasicoherent_of_isCoherent _
  have hpc := RingedSpace.isPseudoCoherent_derivedTensorProduct X.toRingedSpace
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace) K L
    (isPseudoCoherent_of_isBoundedAbove_of_isCoherent_homology X K hKb hKc)
    (isPseudoCoherent_of_isBoundedAbove_of_isCoherent_homology X L hLb hLc)
  obtain ⟨a, ha⟩ := hKb
  obtain ⟨b, hb⟩ := hLb
  have hKLE : K.IsLE a := (DerivedCategory.isLE_iff K a).mpr fun j hj => ha j hj
  have hLLE : L.IsLE b := (DerivedCategory.isLE_iff L b).mpr fun j hj => hb j hj
  have : (((derivedTensor X).obj K).obj L).IsLE (a + b) :=
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _ X.sheaf _ _ _ _ _ _ _
      K L a b hKLE hLLE
  exact ⟨⟨a + b, fun n hn => DerivedCategory.isZero_of_isLE _ (a + b) n hn⟩, fun i =>
    isCoherent_homology_of_isPseudoCoherentFrom X (((derivedTensor X).obj K).obj L) i
      (isQuasicoherent_homology_derivedTensor X K L hKq hLq)
      (hpc.isPseudoCoherentFrom i) i le_rfl⟩

/-! ### Coherence of the Tor sheaves -/

/-- **A module placed in degree `0` is bounded above**, with bound `0`. -/
theorem isBoundedAbove_singleFunctor_obj (X : Scheme.{u}) (F : X.Modules) :
    DerivedCategoryB.IsBoundedAbove ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  ⟨0, fun n hn => DerivedCategory.isZero_of_isLE _ 0 n hn⟩

/-- The cohomology sheaves of a module placed in degree `0` vanish away from degree `0`. -/
private theorem isZero_homology_singleFunctor_obj (X : Scheme.{u}) (F : X.Modules) {i : ℤ}
    (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  rcases hi.lt_or_gt with hi | hi
  exacts [DerivedCategory.isZero_of_isGE _ 0 i hi, DerivedCategory.isZero_of_isLE _ 0 i hi]

/-- **The cohomology sheaves of a coherent module placed in degree `0` are coherent**: the one in
degree `0` is the module itself, and the others vanish. -/
theorem isCoherent_homology_singleFunctor_obj (X : Scheme.{u}) (F : X.Modules)
    (hF : F.IsCoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsCoherent := by
  by_cases hi : i = 0
  · subst hi
    exact (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app F).symm
      hF.stacksIsCoherent).rootIsCoherent
  · exact (Stacks.SheafOfModules.isCoherent_of_isZero
      (isZero_homology_singleFunctor_obj X F hi)).rootIsCoherent

/-- **[Stacks, Tag 0AZS] part (1).** Let `X` be a locally Noetherian scheme. If `ℱ` and `𝒢` are
coherent `𝒪_X`-modules then so is `Tor_p^{𝒪_X}(ℱ, 𝒢)` for every `p`.

A coherent module placed in degree `0` lies in `D⁻_Coh(𝒪_X)`, so part (2) applies to the two
factors and every cohomology sheaf of their derived tensor product is coherent. -/
@[stacks 0AZS "part (1): the Tor sheaves of two coherent modules are coherent"]
theorem isCoherent_torSheaf (X : Scheme.{u}) [IsLocallyNoetherian X] (F G : X.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) (p : ℕ) : (torSheaf X F G p).IsCoherent :=
  (derivedCategoryBMinus_derivedTensor X _ _
    ⟨isBoundedAbove_singleFunctor_obj X F, isCoherent_homology_singleFunctor_obj X F hF⟩
    ⟨isBoundedAbove_singleFunctor_obj X G,
      isCoherent_homology_singleFunctor_obj X G hG⟩).2 (-(p : ℤ))

/-! ### The stalk of a Tor sheaf -/

/-- **The stalk of a Tor sheaf, computed from K-flat representatives.** If `P` and `Q` are
K-flat complexes whose classes in `D(𝒪_X)` are `ℱ` and `𝒢` placed in degree `0`, then the stalk
at `x` of `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the `(-p)`-th cohomology module of the complex of stalks of
`Tot(P ⊗_{𝒪_X} Q)`. -/
def stalkTorSheafIso (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) (x : X)
    (P Q : Stacks.Duality.TensorComplex X)
    (hP : Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf P)
    (hQ : Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf Q)
    (eP : (DerivedCategory.Q.obj P : DerivedCategory X.Modules) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F)
    (eQ : (DerivedCategory.Q.obj Q : DerivedCategory X.Modules) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj G) :
    (Scheme.Modules.stalkFunctor X x).obj (torSheaf X F G p) ≅
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x
        (Stacks.Duality.totalTensorComplex P Q)).homology (-(p : ℤ)) :=
  let O := Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf
  let E := ((derivedTensor X).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj G)
  let eG : (DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex P Q) :
      DerivedCategory X.Modules) ≅ E :=
    ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparison P Q hP hQ).symm ≪≫
      ((derivedTensor X).mapIso eP).app _ ≪≫
      ((derivedTensor X).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)).mapIso eQ
  ((AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso O x (-(p : ℤ))).app E).symm ≪≫
    (DerivedCategory.homologyFunctor _ (-(p : ℤ))).mapIso
      ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor O x).mapIso eG.symm) ≪≫
    (DerivedCategory.homologyFunctor _ (-(p : ℤ))).mapIso
      ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors O x).app
        (Stacks.Duality.totalTensorComplex P Q)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ (-(p : ℤ))).app
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x
        (Stacks.Duality.totalTensorComplex P Q))

/-- **A K-flat representative of a module with vanishing stalk at `x` has acyclic complex of
stalks at `x`.** The cohomology of the complex of stalks is the stalk of the cohomology, and the
cohomology sheaves of a module placed in degree `0` are that module in degree `0` and zero
elsewhere. -/
theorem acyclic_stalkComplex_of_isZero_stalk (X : Scheme.{u}) (F : X.Modules) (x : X)
    (P : Stacks.Duality.TensorComplex X)
    (eP : (DerivedCategory.Q.obj P : DerivedCategory X.Modules) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F)
    (hF : IsZero ((Scheme.Modules.stalkFunctor X x).obj F)) :
    (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x P).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have key : (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x P).homology i ≅
      (Scheme.Modules.stalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
    ((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) x).app P).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) x).mapIso eP) ≪≫
      (AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) x i).app _
  refine IsZero.of_iso ?_ key
  by_cases hi : i = 0
  · subst hi
    exact hF.of_iso ((Scheme.Modules.stalkFunctor X x).mapIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app F))
  · exact Functor.map_isZero (Scheme.Modules.stalkFunctor X x)
      (isZero_homology_singleFunctor_obj X F hi)

/-- A Tor sheaf has vanishing stalk at `x` as soon as `Tot(P_x ⊗ Q_x)` is acyclic for all
K-flat representatives `P` and `Q`. -/
private theorem isZero_stalk_torSheaf_of_acyclic (X : Scheme.{u}) (F G : X.Modules) (p : ℕ)
    (x : X)
    (h : ∀ P Q : Stacks.Duality.TensorComplex X,
      Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf P →
      Stacks.SheafOfModules.KFlat.{u, u, u} X.sheaf Q →
      ((DerivedCategory.Q.obj P : DerivedCategory X.Modules) ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj F) →
      ((DerivedCategory.Q.obj Q : DerivedCategory X.Modules) ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj G) →
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x
        (Stacks.Duality.totalTensorComplex P Q)).Acyclic) :
    IsZero ((Scheme.Modules.stalkFunctor X x).obj (torSheaf X F G p)) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_kFlatComplex_iso X ((DerivedCategory.singleFunctor X.Modules 0).obj F)
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ :=
    exists_kFlatComplex_iso X ((DerivedCategory.singleFunctor X.Modules 0).obj G)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (h P Q hP hQ eP eQ (-(p : ℤ)))).of_iso (stalkTorSheafIso X F G p x P Q hP hQ eP eQ)

/-- **A Tor sheaf has vanishing stalk wherever the first factor does.** A K-flat representative
of `ℱ` has acyclic complex of stalks at such a point, and the total tensor complex of an acyclic
complex with a K-flat one is acyclic. -/
theorem isZero_stalk_torSheaf_of_isZero_stalk_left (X : Scheme.{u}) (F G : X.Modules) (p : ℕ)
    (x : X) (hF : IsZero ((Scheme.Modules.stalkFunctor X x).obj F)) :
    IsZero ((Scheme.Modules.stalkFunctor X x).obj (torSheaf X F G p)) := by
  let _stalkCommRing := StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  refine isZero_stalk_torSheaf_of_acyclic X F G p x fun P Q hP hQ eP _ => ?_
  exact HomologicalComplex.Acyclic.of_iso
    (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso X.sheaf x P Q).symm
    ((Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise X.sheaf Q).mp hQ x
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x P)
      (acyclic_stalkComplex_of_isZero_stalk X F x P eP hF))

/-- **A Tor sheaf has vanishing stalk wherever the second factor does.** The companion of
`isZero_stalk_torSheaf_of_isZero_stalk_left`, using that over a commutative ring a K-flat
complex is K-flat in the left variable of the tensor product as well. -/
theorem isZero_stalk_torSheaf_of_isZero_stalk_right (X : Scheme.{u}) (F G : X.Modules) (p : ℕ)
    (x : X) (hG : IsZero ((Scheme.Modules.stalkFunctor X x).obj G)) :
    IsZero ((Scheme.Modules.stalkFunctor X x).obj (torSheaf X F G p)) := by
  let _stalkCommRing := StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  refine isZero_stalk_torSheaf_of_acyclic X F G p x fun P Q hP _ _ eQ => ?_
  exact HomologicalComplex.Acyclic.of_iso
    (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso X.sheaf x P Q).symm
    (CochainComplex.KFlat.kFlatLeft_of_kFlat
      ((Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise X.sheaf P).mp hP x)
      (AlgebraicGeometry.SheafOfModules.stalkComplex X.sheaf x Q)
      (acyclic_stalkComplex_of_isZero_stalk X G x Q eQ hG))

/-! ### Support and coherence of the Tor sheaves on a regular scheme -/

/-- **[Stacks, Tag 0AZT]: the Tor sheaves are supported on `Supp(ℱ) ∩ Supp(𝒢)`.** Away from
the support of either factor the corresponding stalk vanishes, and then so does the stalk of
every `Tor_p^{𝒪_X}(ℱ, 𝒢)`.

No hypothesis on `X` or on the two modules is needed: the argument is the stalkwise computation
of the derived tensor product on K-flat representatives. -/
@[stacks 0AZT "the Tor sheaves are supported on the intersection of the supports of the two \
modules"]
theorem supp_torSheaf_subset_inter (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) :
    SheafOfModules.supp (torSheaf X F G p) ⊆
      SheafOfModules.supp F ∩ SheafOfModules.supp G := by
  intro x hx
  refine ⟨?_, ?_⟩
  · by_contra hF
    exact (Scheme.Modules.notMem_supp_iff_isZero_stalk (torSheaf X F G p) x).mpr
      (isZero_stalk_torSheaf_of_isZero_stalk_left X F G p x
        ((Scheme.Modules.notMem_supp_iff_isZero_stalk F x).mp hF)) hx
  · by_contra hG
    exact (Scheme.Modules.notMem_supp_iff_isZero_stalk (torSheaf X F G p) x).mpr
      (isZero_stalk_torSheaf_of_isZero_stalk_right X F G p x
        ((Scheme.Modules.notMem_supp_iff_isZero_stalk G x).mp hG)) hx

/-- **[Stacks, Tag 0AZT]: the Tor sheaves of two coherent modules on a regular scheme are
coherent.** A regular — that is, nonsingular — scheme is locally Noetherian, by the
characterization of regularity as local Noetherianity together with regularity of all the local
rings, so [Stacks, Tag 0AZS] part (1) applies. -/
@[stacks 0AZT "the Tor sheaves of two coherent modules on a regular scheme are coherent"]
theorem isCoherent_torSheaf_of_isRegular (X : Scheme.{u}) (hX : IsRegular X)
    (F G : X.Modules) (hF : F.IsCoherent) (hG : G.IsCoherent) (p : ℕ) :
    (torSheaf X F G p).IsCoherent :=
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  isCoherent_torSheaf X F G hF hG p

end

end AlgebraicGeometry.TorFormula

end
