module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectionFormulaKZero.ParityEulerClass
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison
public import StacksFrontier.Homology.Tor.ExtremalDegrees
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness

/-!
# Dévissage of the parity Euler class along an exact functor

Let `X` and `Y` be locally Noetherian schemes and `Φ : D(𝒪_X) ⥤ D(𝒪_Y)` an exact functor which
carries objects with locally bounded coherent cohomology to such objects and commutes with direct
sums of them. For every object `M` of `D(𝒪_X)` with locally bounded coherent cohomology,

  `χ(Φ M) = χ(Φ(⨁_i H^{2i}(M))) − χ(Φ(⨁_i H^{2i+1}(M)))`,

the two sums placed in degree `0`. On a quasi-compact scheme this is the usual dévissage of a
bounded complex by its canonical truncations. In general the truncations of `M` need not
terminate; they are summed instead. The sum `⨁_k τ_{≥2k} M` has locally bounded coherent
cohomology, its distinguished triangle with `⨁_k τ_{≥2k+2} M` and with the sum of the windows
`τ_{<2k+2} τ_{≥2k} M` telescopes, and `χ` of the windows is read off from their cohomology, the
windows being shifted into degrees `0` and `1` by even amounts that `χ` does not see.

## Main results

* `AlgebraicGeometry.ParityEulerClass.parityEulerClass_sigma_shift`: `χ` of a direct sum does
  not change when the summands are shifted by even amounts.
* `AlgebraicGeometry.ParityEulerClass.parityEulerClass_map_eq`: the dévissage above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology

universe u w

namespace AlgebraicGeometry.ParityEulerClass

/-! ### Isomorphisms of coproducts -/

section Coproducts

variable {C : Type*} [Category C]

/-- A coproduct indexed by a sum type is the binary biproduct of the two partial coproducts. -/
def sigmaSumIso [Preadditive C] [HasBinaryBiproducts C] {α β : Type*} (F : α ⊕ β → C)
    [HasCoproduct F] [HasCoproduct fun a => F (Sum.inl a)] [HasCoproduct fun b => F (Sum.inr b)] :
    ∐ F ≅ (∐ fun a => F (Sum.inl a)) ⊞ ∐ fun b => F (Sum.inr b) where
  hom := Limits.Sigma.desc fun s => match s with
    | Sum.inl a => Limits.Sigma.ι (fun a => F (Sum.inl a)) a ≫ biprod.inl
    | Sum.inr b => Limits.Sigma.ι (fun b => F (Sum.inr b)) b ≫ biprod.inr
  inv := biprod.desc (Limits.Sigma.desc fun a => Limits.Sigma.ι F (Sum.inl a))
    (Limits.Sigma.desc fun b => Limits.Sigma.ι F (Sum.inr b))
  hom_inv_id := by
    refine Limits.Sigma.hom_ext _ _ fun s => ?_
    cases s <;> simp
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> exact Limits.Sigma.hom_ext _ _ fun _ => by simp

/-- Interchanging the two summations of an iterated coproduct. -/
def sigmaCommIso {I J : Type*} (F : I → J → C) [∀ i, HasCoproduct (F i)]
    [∀ j, HasCoproduct fun i => F i j] [HasCoproduct fun i => ∐ F i]
    [HasCoproduct fun j => ∐ fun i => F i j] :
    (∐ fun i => ∐ F i) ≅ ∐ fun j => ∐ fun i => F i j where
  hom := Limits.Sigma.desc fun i => Limits.Sigma.desc fun j =>
    Limits.Sigma.ι (fun i => F i j) i ≫ Limits.Sigma.ι (fun j => ∐ fun i => F i j) j
  inv := Limits.Sigma.desc fun j => Limits.Sigma.desc fun i =>
    Limits.Sigma.ι (F i) j ≫ Limits.Sigma.ι (fun i => ∐ F i) i
  hom_inv_id := by
    refine Limits.Sigma.hom_ext _ _ fun i => Limits.Sigma.hom_ext _ _ fun j => ?_
    simp
  inv_hom_id := by
    refine Limits.Sigma.hom_ext _ _ fun j => Limits.Sigma.hom_ext _ _ fun i => ?_
    simp

/-- A coproduct of zero objects is a zero object. -/
theorem isZero_sigma [HasZeroMorphisms C] {J : Type*} (F : J → C) [HasCoproduct F]
    (h : ∀ j, IsZero (F j)) : IsZero (∐ F) := by
  rw [IsZero.iff_id_eq_zero]
  exact Limits.Sigma.hom_ext _ _ fun j => (h j).eq_of_src _ _

/-- The components of `sigmaNatSplit`. -/
def sigmaNatSplitDesc [Preadditive C] [HasBinaryBiproducts C] (A : ULift.{w} ℕ → C)
    [HasCoproduct fun k : ULift.{w} ℕ => A ⟨k.down + 1⟩] :
    (k : ULift.{w} ℕ) → (A k ⟶ A ⟨0⟩ ⊞ ∐ fun k : ULift.{w} ℕ => A ⟨k.down + 1⟩)
  | ⟨0⟩ => biprod.inl
  | ⟨n + 1⟩ => Limits.Sigma.ι (fun k : ULift.{w} ℕ => A ⟨k.down + 1⟩) ⟨n⟩ ≫ biprod.inr

/-- A coproduct indexed by `ℕ` splits off its first summand. -/
def sigmaNatSplit [Preadditive C] [HasBinaryBiproducts C] (A : ULift.{w} ℕ → C) [HasCoproduct A]
    [HasCoproduct fun k : ULift.{w} ℕ => A ⟨k.down + 1⟩] :
    ∐ A ≅ A ⟨0⟩ ⊞ ∐ fun k : ULift.{w} ℕ => A ⟨k.down + 1⟩ where
  hom := Limits.Sigma.desc (sigmaNatSplitDesc A)
  inv := biprod.desc (Limits.Sigma.ι A ⟨0⟩)
    (Limits.Sigma.desc fun k => Limits.Sigma.ι A ⟨k.down + 1⟩)
  hom_inv_id := by
    refine Limits.Sigma.hom_ext _ _ fun k => ?_
    obtain ⟨_ | n⟩ := k <;> simp [sigmaNatSplitDesc]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp [sigmaNatSplitDesc]
    · exact Limits.Sigma.hom_ext _ _ fun k => by simp [sigmaNatSplitDesc]

end Coproducts


/-! ### Supports of finite direct sums -/

section Support

variable {X : Scheme.{u}}

/-- A point is outside the support of a module iff the stalk functor kills the module there. -/
private theorem notMem_supp_iff_isZero_stalkFunctor_obj (M : X.Modules) (x : X) :
    x ∉ SheafOfModules.supp M ↔
      IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M) :=
  ⟨fun h => (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ _ _).2
      (isZero_stalk_of_notMem_supp _ x h),
    fun h => notMem_supp_of_isZero_stalk _ x
      ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ _ _).1 h)⟩

/-- The support of a zero module is empty. -/
theorem supp_eq_empty_of_isZero {M : X.Modules} (hM : IsZero M) : SheafOfModules.supp M = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun x => (notMem_supp_iff_isZero_stalkFunctor_obj M x).2
    ((AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj _ _).1 hM x)

/-- **The support of a finite direct sum is contained in the union of the supports.** The stalk
functor commutes with finite direct sums. -/
theorem supp_sigma_subset {J : Type u} (G : J → X.Modules) [HasCoproduct G] (S : Set J)
    [Finite S] [HasCoproduct fun j : S => G j] (hz : ∀ j, j ∉ S → IsZero (G j)) :
    SheafOfModules.supp (∐ G) ⊆ ⋃ j ∈ S, SheafOfModules.supp (G j) := by
  classical
  intro x hx
  by_contra hn
  simp only [Set.mem_iUnion, not_exists] at hn
  have hx' : x ∈ SheafOfModules.supp (∐ fun j : S => G j) :=
    (SheafOfModules.supp_eq_of_iso (sigmaSubtypeIsoOfIsZero G S hz)).ge hx
  have : Fintype S := Fintype.ofFinite S
  let F := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hz' : IsZero (F.obj (∐ fun j : S => G j)) :=
    IsZero.of_iso (isZero_sigma _ fun j : S =>
      (notMem_supp_iff_isZero_stalkFunctor_obj _ x).1 (hn j j.2))
      (PreservesCoproduct.iso F fun j : S => G j)
  exact (notMem_supp_iff_isZero_stalkFunctor_obj _ x).2 hz' hx'

end Support

/-! ### Objects with locally bounded coherent cohomology -/

section LocallyBounded

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The cohomology of a direct sum in the derived category is the sum of the cohomologies. -/
private def homologyFunctorSigmaIso {J : Type u} (K : J → DerivedCategory X.Modules) (n : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules n).obj (∐ K) ≅
      ∐ fun j => (DerivedCategory.homologyFunctor X.Modules n).obj (K j) :=
  have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor X.Modules (J := J) n
  PreservesCoproduct.iso _ K

/-- **Locally bounded coherent cohomology is detected degree by degree**: if each cohomology
sheaf of `L` vanishes or is isomorphic to the cohomology sheaf of `K` in a degree depending
injectively on the degree, and `K` has locally bounded coherent cohomology, so has `L`. -/
theorem IsLocallyBoundedCoherent.of_homology {K L : DerivedCategory X.Modules}
    (hK : IsLocallyBoundedCoherent K) (σ : ℤ → ℤ) (hσ : Function.Injective σ)
    (h : ∀ n, IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj L) ∨
      Nonempty ((DerivedCategory.homologyFunctor X.Modules n).obj L ≅
        (DerivedCategory.homologyFunctor X.Modules (σ n)).obj K)) :
    IsLocallyBoundedCoherent L := by
  refine ⟨fun n => ?_, (hK.2.comp_injective hσ).subset fun n => ?_⟩
  · rcases h n with hz | hne
    · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero hz
    · obtain ⟨e⟩ := hne
      exact ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M) e.symm
        (hK.1 (σ n))
  · rcases h n with hz | hne
    · exact (supp_eq_empty_of_isZero hz).le.trans (Set.empty_subset _)
    · obtain ⟨e⟩ := hne
      exact (SheafOfModules.supp_eq_of_iso e).le

/-- **A direct sum has locally bounded coherent cohomology** when in each degree only finitely
many summands have nonzero cohomology and the supports of all of them lie in those of one object
with locally bounded coherent cohomology. -/
theorem isLocallyBoundedCoherent_sigma {J : Type u} (K : J → DerivedCategory X.Modules)
    (M : DerivedCategory X.Modules) (hM : IsLocallyBoundedCoherent M)
    (hK : ∀ j n, ((DerivedCategory.homologyFunctor X.Modules n).obj (K j)).IsCoherent)
    (hsupp : ∀ j n, SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj (K j)) ⊆
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj M))
    (hfin : ∀ n, {j | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j))}.Finite) :
    IsLocallyBoundedCoherent (∐ K) := by
  classical
  have hz : ∀ n j, j ∉ {j | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j))} →
      IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j)) := fun n j hj => by
    simpa using hj
  refine ⟨fun n => ?_, hM.2.subset fun n => ?_⟩
  · have : Finite {j | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j))} :=
      (hfin n).to_subtype
    refine ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M)
      ((sigmaSubtypeIsoOfIsZero _ _ (hz n)).trans (homologyFunctorSigmaIso K n).symm) ?_
    exact CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.SheafOfModules.isCoherent_sigma _ fun j =>
        CoherentAbelian.stacksIsCoherent_of_isCoherent (hK j.1 n))
  · have : Finite {j | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j))} :=
      (hfin n).to_subtype
    refine (SheafOfModules.supp_eq_of_iso (homologyFunctorSigmaIso K n)).le.trans
      ((supp_sigma_subset _ _ (hz n)).trans ?_)
    exact Set.iUnion₂_subset fun j _ => hsupp j n

/-- **A direct sum has locally bounded coherent cohomology** when all summands vanish in the
degrees outside a finite set and, in each degree, the supports of their cohomology sheaves form a
locally finite family. -/
theorem isLocallyBoundedCoherent_sigma_of_degrees {J : Type u}
    (K : J → DerivedCategory X.Modules)
    (hK : ∀ j n, ((DerivedCategory.homologyFunctor X.Modules n).obj (K j)).IsCoherent)
    (N : Finset ℤ)
    (hN : ∀ j n, n ∉ N → IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j)))
    (hlf : ∀ n, LocallyFinite fun j =>
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj (K j))) :
    IsLocallyBoundedCoherent (∐ K) := by
  refine ⟨fun n => ?_, fun x => ⟨Set.univ, Filter.univ_mem, (N.finite_toSet).subset fun n hn => ?_⟩⟩
  · exact ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M)
      (homologyFunctorSigmaIso K n).symm
      (isCoherent_sigma_of_locallyFinite _ (fun j => hK j n) (hlf n))
  · by_contra hnN
    have hz : IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (∐ K)) :=
      IsZero.of_iso (isZero_sigma _ fun j => hN j n hnN) (homologyFunctorSigmaIso K n)
    obtain ⟨y, hy, -⟩ := hn
    exact (supp_eq_empty_of_isZero hz).le hy

/-- The cohomology of `τ_{≥ a} K` is that of `K` in the degrees `≥ a` and zero below. -/
theorem homology_truncGE (K : DerivedCategory X.Modules) (a n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj K)) ∨
      Nonempty ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj K) ≅
          (DerivedCategory.homologyFunctor X.Modules n).obj K) := by
  rcases lt_or_ge n a with h | h
  · exact Or.inl (DerivedCategory.isZero_of_isGE _ a n h)
  · have := StacksDraft.ExtremalDegrees.isIso_homology_truncGE a n h K
    exact Or.inr ⟨(asIso ((DerivedCategory.homologyFunctor X.Modules n).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app K))).symm⟩

/-- The cohomology of `τ_{< b} K` is that of `K` in the degrees `< b` and zero above. -/
theorem homology_truncLT (K : DerivedCategory X.Modules) (b n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncLT b).obj K)) ∨
      Nonempty ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncLT b).obj K) ≅
          (DerivedCategory.homologyFunctor X.Modules n).obj K) := by
  rcases lt_or_ge n b with h | h
  · have := StacksDraft.ExtremalDegrees.isIso_homology_truncLT b n h K
    exact Or.inr ⟨asIso ((DerivedCategory.homologyFunctor X.Modules n).map
      ((DerivedCategory.TStructure.t.truncLTι b).app K))⟩
  · exact Or.inl (DerivedCategory.isZero_of_isLE _ (b - 1) n (by omega))

/-- If `K` has locally bounded coherent cohomology, then so does its truncation `τ_{≥ a} K`. -/
theorem IsLocallyBoundedCoherent.truncGE {K : DerivedCategory X.Modules}
    (hK : IsLocallyBoundedCoherent K) (a : ℤ) :
    IsLocallyBoundedCoherent ((DerivedCategory.TStructure.t.truncGE a).obj K) :=
  hK.of_homology id Function.injective_id (homology_truncGE K a)

/-- If `K` has locally bounded coherent cohomology, then so does its truncation `τ_{< b} K`. -/
theorem IsLocallyBoundedCoherent.truncLT {K : DerivedCategory X.Modules}
    (hK : IsLocallyBoundedCoherent K) (b : ℤ) :
    IsLocallyBoundedCoherent ((DerivedCategory.TStructure.t.truncLT b).obj K) :=
  hK.of_homology id Function.injective_id (homology_truncLT K b)

/-- An object with locally bounded coherent cohomology stays so after a shift. -/
theorem IsLocallyBoundedCoherent.shift {K : DerivedCategory X.Modules}
    (hK : IsLocallyBoundedCoherent K) (a : ℤ) : IsLocallyBoundedCoherent (K⟦a⟧) :=
  hK.of_homology (fun n => a + n) (add_right_injective a) fun n =>
    Or.inr ⟨((DerivedCategory.homologyFunctor X.Modules 0).shiftIso a n (a + n) rfl).app K⟩

/-- The zero object has locally bounded coherent cohomology. -/
theorem isLocallyBoundedCoherent_of_isZero {K : DerivedCategory X.Modules} (hK : IsZero K) :
    IsLocallyBoundedCoherent K := by
  have hz : ∀ n, IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj K) := fun n =>
    Functor.map_isZero _ hK
  exact ⟨fun n => Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero (hz n), fun x =>
    ⟨Set.univ, Filter.univ_mem, by simp [supp_eq_empty_of_isZero (hz _)]⟩⟩

/-- A coherent module placed in degree `0` has locally bounded coherent cohomology. -/
theorem isLocallyBoundedCoherent_single (F : X.Modules) (hF : F.IsCoherent) :
    IsLocallyBoundedCoherent ((DerivedCategory.singleFunctor X.Modules 0).obj F) := by
  refine ⟨TorFormula.isCoherent_homology_singleFunctor_obj X F hF, fun x =>
    ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton (0 : ℤ)).subset fun n hn => ?_⟩⟩
  by_contra h0
  have hz := ProperPushforwardKZero.isZero_homologyFunctor_obj_singleFunctor_obj F n h0
  simp [supp_eq_empty_of_isZero hz] at hn

/-- Composing two "zero or isomorphic" statements. -/
private theorem isZero_or_nonempty_iso_trans {M N P : X.Modules} (h : IsZero M ∨ Nonempty (M ≅ N))
    (h' : IsZero N ∨ Nonempty (N ≅ P)) : IsZero M ∨ Nonempty (M ≅ P) := by
  rcases h with h | ⟨⟨e⟩⟩
  · exact Or.inl h
  · rcases h' with h' | ⟨⟨e'⟩⟩
    · exact Or.inl (IsZero.of_iso h' e)
    · exact Or.inr ⟨e ≪≫ e'⟩

/-- The cohomology of a truncation in a window `[a, b)`: that of `K` inside the window. -/
theorem homology_truncLT_truncGE (K : DerivedCategory X.Modules) (a b n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncLT b).obj
          ((DerivedCategory.TStructure.t.truncGE a).obj K))) ∨
      Nonempty ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncLT b).obj
          ((DerivedCategory.TStructure.t.truncGE a).obj K)) ≅
          (DerivedCategory.homologyFunctor X.Modules n).obj K) := by
  exact isZero_or_nonempty_iso_trans
    (homology_truncLT ((DerivedCategory.TStructure.t.truncGE a).obj K) b n) (homology_truncGE K a n)

/-- The cohomology of a truncation in a window `[a, b)`, the other order. -/
theorem homology_truncGE_truncLT (K : DerivedCategory X.Modules) (a b n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj
          ((DerivedCategory.TStructure.t.truncLT b).obj K))) ∨
      Nonempty ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj
          ((DerivedCategory.TStructure.t.truncLT b).obj K)) ≅
          (DerivedCategory.homologyFunctor X.Modules n).obj K) := by
  exact isZero_or_nonempty_iso_trans
    (homology_truncGE ((DerivedCategory.TStructure.t.truncLT b).obj K) a n) (homology_truncLT K b n)

/-- If `M` is zero or isomorphic to `N`, then the support of `M` is contained in that of `N`. -/
theorem supp_subset_of_isZero_or_iso {M N : X.Modules} (h : IsZero M ∨ Nonempty (M ≅ N)) :
    SheafOfModules.supp M ⊆ SheafOfModules.supp N := by
  rcases h with h | he
  · exact (supp_eq_empty_of_isZero h).le.trans (Set.empty_subset _)
  · obtain ⟨e⟩ := he
    exact (SheafOfModules.supp_eq_of_iso e).le

/-- A module that is zero or isomorphic to a coherent module `N` is coherent. -/
theorem isCoherent_of_isZero_or_iso {M N : X.Modules} (h : IsZero M ∨ Nonempty (M ≅ N))
    (hN : N.IsCoherent) : M.IsCoherent := by
  rcases h with h | he
  · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero h
  · obtain ⟨e⟩ := he
    exact ObjectProperty.prop_of_iso (P := fun M => SheafOfModules.IsCoherent M) e.symm hN

/-- **A direct sum has locally bounded coherent cohomology** when the cohomology of each summand is
zero or that of one object with locally bounded coherent cohomology, and finitely many summands
have nonzero cohomology in each degree. -/
private theorem isLocallyBoundedCoherent_sigma_of_isZero_or_iso {J : Type u}
    (K : J → DerivedCategory X.Modules) (M : DerivedCategory X.Modules)
    (hM : IsLocallyBoundedCoherent M)
    (h : ∀ j n, IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j)) ∨
      Nonempty ((DerivedCategory.homologyFunctor X.Modules n).obj (K j) ≅
        (DerivedCategory.homologyFunctor X.Modules n).obj M))
    (hfin : ∀ n, {j | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj (K j))}.Finite) :
    IsLocallyBoundedCoherent (∐ K) :=
  isLocallyBoundedCoherent_sigma K M hM
    (fun j n => isCoherent_of_isZero_or_iso (h j n) (hM.1 n))
    (fun j n => supp_subset_of_isZero_or_iso (h j n)) hfin

/-- The indices `k` with `c ≤ 2k` for a fixed bound are finitely many. -/
theorem finite_setOf_two_mul_le (c : ℤ) :
    {k : ULift.{u} ℕ | 2 * (k.down : ℤ) ≤ c}.Finite := by
  refine ((Set.finite_Iic c.toNat).image fun n => (⟨n⟩ : ULift.{u} ℕ)).subset fun k hk => ?_
  refine ⟨k.down, ?_, rfl⟩
  simp only [Set.mem_setOf_eq] at hk
  simp only [Set.mem_Iic]
  omega

/-- The indices `k` with `- 2k ≥ c` for a fixed bound are finitely many. -/
theorem finite_setOf_le_neg_two_mul (c : ℤ) :
    {k : ULift.{u} ℕ | c ≤ -(2 * (k.down : ℤ))}.Finite :=
  (finite_setOf_two_mul_le (-c)).subset fun k hk => by
    simp only [Set.mem_setOf_eq] at hk ⊢
    omega

end LocallyBounded

/-! ### Two-out-of-three, shifts, and even shifts of direct sums -/

section EulerShift

attribute [local instance 100000] HasDerivedCategory.standard

open ZeroObject

variable {X : Scheme.{u}}

/-- The union of two locally finite families of sets, index by index, is locally finite. -/
theorem locallyFinite_union {ι : Type*} {f g : ι → Set X} (hf : LocallyFinite f)
    (hg : LocallyFinite g) : LocallyFinite fun i => f i ∪ g i := by
  intro x
  obtain ⟨s₁, hs₁, hf₁⟩ := hf x
  obtain ⟨s₂, hs₂, hg₂⟩ := hg x
  refine ⟨s₁ ∩ s₂, Filter.inter_mem hs₁ hs₂, (hf₁.union hg₂).subset fun i hi => ?_⟩
  obtain ⟨y, hy, hy₁, hy₂⟩ := hi
  rcases hy with hy | hy
  · exact Or.inl ⟨y, hy, hy₁⟩
  · exact Or.inr ⟨y, hy, hy₂⟩

/-- **Two out of three**: the middle vertex of a distinguished triangle whose outer vertices have
locally bounded coherent cohomology has locally bounded coherent cohomology. Coherent modules
form a weak Serre subcategory, and the stalk functors are exact. -/
theorem IsLocallyBoundedCoherent.obj₂ (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang _) (h₁ : IsLocallyBoundedCoherent T.obj₁)
    (h₃ : IsLocallyBoundedCoherent T.obj₃) : IsLocallyBoundedCoherent T.obj₂ := by
  refine ⟨?_, (locallyFinite_union h₁.2 h₃.2).subset fun n => ?_⟩
  · have := DerivedCategoryB.derivedCategoryB_isTriangulated (fun M : X.Modules => M.IsCoherent)
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre X)
    have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
      (fun M : X.Modules => M.IsCoherent)
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre X)
    exact (DerivedCategoryB.derivedCategoryB
      (fun M : X.Modules => M.IsCoherent)).ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1
  · intro x hx
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    have hex := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
      (O := X.ringCatSheaf) _).1 (DerivedCategory.HomologySequence.exact₂ T hT n) x
    exact (notMem_supp_iff_isZero_stalkFunctor_obj _ x).2 (hex.isZero_of_both_isZero
      ((notMem_supp_iff_isZero_stalkFunctor_obj _ x).1 hn.1)
      ((notMem_supp_iff_isZero_stalkFunctor_obj _ x).1 hn.2)) hx

/-- A biproduct of objects with locally bounded coherent cohomology has locally bounded
coherent cohomology. -/
theorem IsLocallyBoundedCoherent.biprod {A B : DerivedCategory X.Modules}
    (hA : IsLocallyBoundedCoherent A) (hB : IsLocallyBoundedCoherent B) :
    IsLocallyBoundedCoherent (A ⊞ B) :=
  IsLocallyBoundedCoherent.obj₂ _ (binaryBiproductTriangle_distinguished A B) hA hB

/-- The parity Euler class of a zero object vanishes. -/
theorem parityEulerClass_of_isZero [IsLocallyNoetherian X] {K : DerivedCategory X.Modules}
    (hK : IsZero K) :
    parityEulerClass K = 0 := by
  have hz := isLocallyBoundedCoherent_of_isZero hK
  have h := parityEulerClass_obj₂ (contractibleTriangle K) (contractible_distinguished K) hz hz
    (isLocallyBoundedCoherent_of_isZero (isZero_zero _))
  have h0 : parityEulerClass ((contractibleTriangle K).obj₃) = parityEulerClass K :=
    parityEulerClass_congr ((isZero_zero _).iso hK)
  change parityEulerClass K = parityEulerClass K + parityEulerClass ((contractibleTriangle K).obj₃)
    at h
  rw [h0] at h
  simpa using h

/-- **The parity Euler class changes sign under the shift by one.** -/
theorem parityEulerClass_shift_one [IsLocallyNoetherian X] {K : DerivedCategory X.Modules}
    (hK : IsLocallyBoundedCoherent K) : parityEulerClass (K⟦(1 : ℤ)⟧) = -parityEulerClass K := by
  have h := parityEulerClass_obj₂ _ (contractible_distinguished₂ K) hK
    (isLocallyBoundedCoherent_of_isZero (isZero_zero _)) (hK.shift 1)
  change parityEulerClass (0 : DerivedCategory X.Modules) = parityEulerClass K +
    parityEulerClass (K⟦(1 : ℤ)⟧) at h
  rw [parityEulerClass_of_isZero (isZero_zero _)] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **The parity Euler class changes sign under the shift by minus one.** -/
theorem parityEulerClass_shift_neg_one [IsLocallyNoetherian X] {K : DerivedCategory X.Modules}
    (hK : IsLocallyBoundedCoherent K) :
    parityEulerClass (K⟦(-1 : ℤ)⟧) = -parityEulerClass K := by
  have h := parityEulerClass_shift_one (hK.shift (-1))
  have e : (K⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ K :=
    (shiftFunctorCompIsoId (DerivedCategory X.Modules) (-1 : ℤ) 1 (by norm_num)).app K
  rw [parityEulerClass_congr e] at h
  rw [h, neg_neg]

/-- **Shifting the summands of a direct sum by even amounts does not change its parity Euler
class.** In each degree the cohomology of the sum is the sum of the cohomologies, and an even
shift only renumbers the degrees of a summand within one parity. -/
theorem parityEulerClass_sigma_shift {J : Type u} (Z : J → DerivedCategory X.Modules)
    (m : J → ℤ) (h : IsLocallyBoundedCoherent (∐ Z))
    (h' : IsLocallyBoundedCoherent (∐ fun j => (Z j)⟦2 * m j⟧)) :
    parityEulerClass (∐ fun j => (Z j)⟦2 * m j⟧) = parityEulerClass (∐ Z) := by
  have key : ∀ r : ℤ, paritySum (∐ fun j => (Z j)⟦2 * m j⟧) r ≅ paritySum (∐ Z) r := fun r =>
    Limits.Sigma.mapIso (fun i => homologyFunctorSigmaIso _ (2 * i + r)) ≪≫
      Limits.Sigma.mapIso (fun i => Limits.Sigma.mapIso fun j =>
        ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso (2 * m j) (2 * i + r)
          (2 * (i + m j) + r) (by ring)).app (Z j)) ≪≫
      sigmaCommIso _ ≪≫
      Limits.Sigma.mapIso (fun j => Limits.Sigma.reindex (Equiv.addRight (m j))
        (fun i => (DerivedCategory.homologyFunctor X.Modules (2 * i + r)).obj (Z j))) ≪≫
      (sigmaCommIso _).symm ≪≫
      Limits.Sigma.mapIso (fun i => (homologyFunctorSigmaIso Z (2 * i + r)).symm)
  rw [parityEulerClass_eq h', parityEulerClass_eq h,
    KZero.mk_eq_of_iso (ObjectProperty.isoMk (X := parityObject _ h' 0)
      (Y := parityObject (∐ Z) h 0) _ (key 0)),
    KZero.mk_eq_of_iso (ObjectProperty.isoMk (X := parityObject _ h' 1)
      (Y := parityObject (∐ Z) h 1) _ (key 1))]

/-- An object concentrated in one degree is its cohomology sheaf placed in that degree. -/
theorem nonempty_iso_singleFunctor_homology (K : DerivedCategory X.Modules) (n : ℤ) [K.IsGE n]
    [K.IsLE n] : Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules n).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj K)) := by
  obtain ⟨Y, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor X.Modules n).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules n).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules n).mapIso e.symm)⟩

end EulerShift

/-! ### The dévissage along an exact functor -/

section Devissage

attribute [local instance 100000] HasDerivedCategory.standard

open ZeroObject

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (Φ : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ K, IsLocallyBoundedCoherent K → IsLocallyBoundedCoherent (Φ.obj K))

include hΦ

/-- `χ ∘ Φ` is additive along distinguished triangles of objects with locally bounded coherent
cohomology. -/
theorem map_obj₂ (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang _)
    (h₁ : IsLocallyBoundedCoherent T.obj₁) (h₃ : IsLocallyBoundedCoherent T.obj₃) :
    parityEulerClass (Φ.obj T.obj₂) =
      parityEulerClass (Φ.obj T.obj₁) + parityEulerClass (Φ.obj T.obj₃) :=
  parityEulerClass_obj₂ (Φ.mapTriangle.obj T) (Φ.map_distinguished T hT) (hΦ _ h₁)
    (hΦ _ (IsLocallyBoundedCoherent.obj₂ T hT h₁ h₃)) (hΦ _ h₃)

/-- `χ ∘ Φ` is additive on biproducts. -/
theorem map_biprod {A B : DerivedCategory X.Modules} (hA : IsLocallyBoundedCoherent A)
    (hB : IsLocallyBoundedCoherent B) :
    parityEulerClass (Φ.obj (A ⊞ B)) = parityEulerClass (Φ.obj A) + parityEulerClass (Φ.obj B) :=
  map_obj₂ Φ hΦ _ (binaryBiproductTriangle_distinguished A B) hA hB

/-- **The telescope.** If `χ(Φ(⨁_k A_k)) = χ(Φ(⨁_k A_{k+1})) + χ(Φ S)`, then
`χ(Φ A₀) = χ(Φ S)`: the first sum is `A₀ ⊕ ⨁_k A_{k+1}`, and `χ ∘ Φ` is additive on it. -/
theorem map_telescope (A : ULift.{u} ℕ → DerivedCategory X.Modules) (S : DerivedCategory X.Modules)
    (hA' : IsLocallyBoundedCoherent (∐ fun k : ULift.{u} ℕ => A ⟨k.down + 1⟩))
    (hA₀ : IsLocallyBoundedCoherent (A ⟨0⟩))
    (hadd : parityEulerClass (Φ.obj (∐ A)) = parityEulerClass
      (Φ.obj (∐ fun k : ULift.{u} ℕ => A ⟨k.down + 1⟩)) + parityEulerClass (Φ.obj S)) :
    parityEulerClass (Φ.obj (A ⟨0⟩)) = parityEulerClass (Φ.obj S) := by
  have h := map_biprod Φ hΦ hA₀ hA'
  rw [← parityEulerClass_congr (Φ.mapIso (sigmaNatSplit A)), hadd] at h
  exact (add_left_cancel (h.trans (add_comm _ _))).symm

/-- **The telescope in degrees `≥ 0`.** `χ(Φ(τ_{≥0} M))` is `χ ∘ Φ` of the sum of the windows
`τ_{<2k+2} τ_{≥2k} M`. -/
theorem map_truncGE_zero (M : DerivedCategory X.Modules) (hM : IsLocallyBoundedCoherent M) :
    parityEulerClass (Φ.obj ((DerivedCategory.TStructure.t.truncGE 0).obj M)) =
      parityEulerClass (Φ.obj (∐ fun k : ULift.{u} ℕ =>
        (DerivedCategory.TStructure.t.truncLT (2 * ((k.down + 1 : ℕ) : ℤ))).obj
          ((DerivedCategory.TStructure.t.truncGE (2 * (k.down : ℤ))).obj M))) := by
  let t := DerivedCategory.TStructure.t (C := X.Modules)
  let A : ULift.{u} ℕ → DerivedCategory X.Modules := fun k =>
    (t.truncGE (2 * (k.down : ℤ))).obj M
  let T : ULift.{u} ℕ → Triangle (DerivedCategory X.Modules) := fun k =>
    (t.triangleLTGE (2 * ((k.down + 1 : ℕ) : ℤ))).obj (A k)
  have hT := coproductTriangle_distinguished T fun k => t.triangleLTGE_distinguished _ _
  have e₃ : (∐ fun k => (T k).obj₃) ≅ ∐ fun k : ULift.{u} ℕ => A ⟨k.down + 1⟩ :=
    Limits.Sigma.mapIso fun k =>
      have := t.isIso_truncGE_map_truncGEπ_app (2 * ((k.down + 1 : ℕ) : ℤ))
        (2 * (k.down : ℤ)) (by push_cast; omega) M
      (asIso ((t.truncGE (2 * ((k.down + 1 : ℕ) : ℤ))).map
        ((t.truncGEπ (2 * (k.down : ℤ))).app M))).symm
  have hA : ∀ c : ULift.{u} ℕ → ℤ, (∀ k, 2 * (k.down : ℤ) ≤ c k) →
      IsLocallyBoundedCoherent (∐ fun k => (t.truncGE (c k)).obj M) := fun c hc =>
    isLocallyBoundedCoherent_sigma_of_isZero_or_iso _ M hM (fun k n => homology_truncGE M _ n)
      fun n => (finite_setOf_two_mul_le n).subset fun k hk => by
        by_contra hlt
        exact hk (DerivedCategory.isZero_of_isGE _ (c k) n
          (by simp only [Set.mem_setOf_eq, not_le] at hlt; linarith [hc k]))
  have hA' : IsLocallyBoundedCoherent (∐ fun k : ULift.{u} ℕ => A ⟨k.down + 1⟩) :=
    hA (fun k => 2 * ((k.down + 1 : ℕ) : ℤ)) fun k => by push_cast; omega
  have hW : IsLocallyBoundedCoherent (∐ fun k => (T k).obj₁) :=
    isLocallyBoundedCoherent_sigma_of_isZero_or_iso _ M hM
      (fun k n => homology_truncLT_truncGE M _ _ n)
      fun n => (finite_setOf_two_mul_le n).subset fun k hk => by
        by_contra hlt
        simp only [Set.mem_setOf_eq, not_le] at hlt
        have : DerivedCategory.IsGE ((T k).obj₁) (2 * (k.down : ℤ)) :=
          show t.IsGE ((t.truncLT _).obj (A k)) _ from inferInstance
        exact hk (DerivedCategory.isZero_of_isGE _ (2 * (k.down : ℤ)) n hlt)
  have hadd := map_obj₂ Φ hΦ _ hT hW (hA'.of_iso e₃.symm)
  change parityEulerClass (Φ.obj (∐ fun k => (T k).obj₂)) =
    parityEulerClass (Φ.obj (∐ fun k => (T k).obj₁)) +
      parityEulerClass (Φ.obj (∐ fun k => (T k).obj₃)) at hadd
  rw [parityEulerClass_congr (Φ.mapIso e₃), add_comm] at hadd
  exact map_telescope Φ hΦ A _ hA' (hM.truncGE _) hadd

/-- **The telescope in degrees `< 0`.** `χ(Φ(τ_{<0} M))` is `χ ∘ Φ` of the sum of the windows
`τ_{≥ -2k-2} τ_{< -2k} M`. -/
theorem map_truncLT_zero (M : DerivedCategory X.Modules) (hM : IsLocallyBoundedCoherent M) :
    parityEulerClass (Φ.obj ((DerivedCategory.TStructure.t.truncLT 0).obj M)) =
      parityEulerClass (Φ.obj (∐ fun k : ULift.{u} ℕ =>
        (DerivedCategory.TStructure.t.truncGE (-(2 * ((k.down + 1 : ℕ) : ℤ)))).obj
          ((DerivedCategory.TStructure.t.truncLT (-(2 * (k.down : ℤ)))).obj M))) := by
  let t := DerivedCategory.TStructure.t (C := X.Modules)
  let A : ULift.{u} ℕ → DerivedCategory X.Modules := fun k =>
    (t.truncLT (-(2 * (k.down : ℤ)))).obj M
  let T : ULift.{u} ℕ → Triangle (DerivedCategory X.Modules) := fun k =>
    (t.triangleLTLTGELT (-(2 * ((k.down + 1 : ℕ) : ℤ))) (-(2 * (k.down : ℤ)))
      (by push_cast; omega)).obj M
  have hT := coproductTriangle_distinguished T fun k => t.triangleLTLTGELT_distinguished _ _ _ _
  have hA : ∀ c : ULift.{u} ℕ → ℤ, (∀ k, c k ≤ -(2 * (k.down : ℤ))) →
      IsLocallyBoundedCoherent (∐ fun k => (t.truncLT (c k)).obj M) := fun c hc =>
    isLocallyBoundedCoherent_sigma_of_isZero_or_iso _ M hM (fun k n => homology_truncLT M _ n)
      fun n => (finite_setOf_le_neg_two_mul (n + 1)).subset fun k hk => by
        by_contra hlt
        simp only [Set.mem_setOf_eq, not_le] at hlt
        exact hk (DerivedCategory.isZero_of_isLE _ (c k - 1) n (by linarith [hc k]))
  have hA' : IsLocallyBoundedCoherent (∐ fun k : ULift.{u} ℕ => A ⟨k.down + 1⟩) :=
    hA (fun k => -(2 * ((k.down + 1 : ℕ) : ℤ))) fun k => by push_cast; omega
  have hW : IsLocallyBoundedCoherent (∐ fun k => (T k).obj₃) :=
    isLocallyBoundedCoherent_sigma_of_isZero_or_iso _ M hM
      (fun k n => homology_truncGE_truncLT M _ _ n)
      fun n => (finite_setOf_le_neg_two_mul (n + 1)).subset fun k hk => by
        by_contra hlt
        simp only [Set.mem_setOf_eq, not_le] at hlt
        have : DerivedCategory.IsLE ((T k).obj₃) (-(2 * (k.down : ℤ)) - 1) :=
          show t.IsLE ((t.truncGELT _ _).obj M) _ from inferInstance
        exact hk (DerivedCategory.isZero_of_isLE _ (-(2 * (k.down : ℤ)) - 1) n (by linarith))
  have hadd := map_obj₂ Φ hΦ _ hT hA' hW
  exact map_telescope Φ hΦ A _ hA' (hM.truncLT _) hadd

variable (hΦσ : ∀ K : ULift.{u} ℕ → DerivedCategory X.Modules,
  (∀ k, IsLocallyBoundedCoherent (K k)) → IsIso (sigmaComparison Φ K))

include hΦσ in
omit [IsLocallyNoetherian Y] [Φ.IsTriangulated] in
/-- **Even shifts of the summands do not change `χ ∘ Φ` of a direct sum.** -/
theorem map_sigma_shift (W : ULift.{u} ℕ → DerivedCategory X.Modules) (m : ULift.{u} ℕ → ℤ)
    (hW : ∀ k, IsLocallyBoundedCoherent (W k)) (h : IsLocallyBoundedCoherent (∐ W))
    (h' : IsLocallyBoundedCoherent (∐ fun k => (W k)⟦2 * m k⟧)) :
    parityEulerClass (Φ.obj (∐ W)) = parityEulerClass (Φ.obj (∐ fun k => (W k)⟦2 * m k⟧)) := by
  have := hΦσ W hW
  have := hΦσ (fun k => (W k)⟦2 * m k⟧) fun k => (hW k).shift _
  let e₁ : Φ.obj (∐ W) ≅ ∐ fun k => Φ.obj (W k) := (asIso (sigmaComparison Φ W)).symm
  let e₂ : Φ.obj (∐ fun k => (W k)⟦2 * m k⟧) ≅ ∐ fun k => (Φ.obj (W k))⟦2 * m k⟧ :=
    (asIso (sigmaComparison Φ _)).symm ≪≫
      Limits.Sigma.mapIso fun k => (Φ.commShiftIso (2 * m k)).app (W k)
  rw [parityEulerClass_congr e₁, parityEulerClass_congr e₂]
  exact (parityEulerClass_sigma_shift (fun k => Φ.obj (W k)) m ((hΦ _ h).of_iso e₁)
    ((hΦ _ h').of_iso e₂)).symm

/-- The sum `⨁_{i ∈ ℤ} H^{2i+r}(M)` split into the terms with `i ≥ 0` and those with `i < 0`. -/
def paritySumSplit (M : DerivedCategory X.Modules) (r : ℤ) :
    paritySum M r ≅
      (∐ fun k : ULift.{u} ℕ =>
        (DerivedCategory.homologyFunctor X.Modules (2 * (k.down : ℤ) + r)).obj M) ⊞
      (∐ fun k : ULift.{u} ℕ =>
        (DerivedCategory.homologyFunctor X.Modules (2 * (-((k.down + 1 : ℕ) : ℤ)) + r)).obj M) :=
  (Limits.Sigma.reindex ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
      Equiv.intEquivNatSumNat.symm)
    (fun i : ℤ => (DerivedCategory.homologyFunctor X.Modules (2 * i + r)).obj M)).symm ≪≫
    sigmaSumIso _

include hΦσ in
/-- **The dévissage of `χ ∘ Φ`.** For an exact functor `Φ` carrying objects with locally bounded
coherent cohomology to such objects and commuting with direct sums of them,

  `χ(Φ M) = χ(Φ(⨁_i H^{2i}(M))) − χ(Φ(⨁_i H^{2i+1}(M)))`

for every `M` with locally bounded coherent cohomology, the sums placed in degree `0`. -/
theorem parityEulerClass_map_eq (M : DerivedCategory X.Modules)
    (hM : IsLocallyBoundedCoherent M) :
    parityEulerClass (Φ.obj M) =
      parityEulerClass (Φ.obj ((DerivedCategory.singleFunctor X.Modules 0).obj (paritySum M 0))) -
        parityEulerClass
          (Φ.obj ((DerivedCategory.singleFunctor X.Modules 0).obj (paritySum M 1))) := by
  let t := DerivedCategory.TStructure.t (C := X.Modules)
  let H := fun n : ℤ => DerivedCategory.homologyFunctor X.Modules n
  let W : ULift.{u} ℕ → DerivedCategory X.Modules := fun k =>
    (t.truncLT (2 * ((k.down + 1 : ℕ) : ℤ))).obj ((t.truncGE (2 * (k.down : ℤ))).obj M)
  let W' : ULift.{u} ℕ → DerivedCategory X.Modules := fun k =>
    (t.truncGE (-(2 * ((k.down + 1 : ℕ) : ℤ)))).obj ((t.truncLT (-(2 * (k.down : ℤ)))).obj M)
  let m : ULift.{u} ℕ → ℤ := fun k => (k.down : ℤ)
  let m' : ULift.{u} ℕ → ℤ := fun k => -((k.down + 1 : ℕ) : ℤ)
  let V : ULift.{u} ℕ → DerivedCategory X.Modules := fun k => (W k)⟦2 * m k⟧
  let V' : ULift.{u} ℕ → DerivedCategory X.Modules := fun k => (W' k)⟦2 * m' k⟧
  have hWk : ∀ k, IsLocallyBoundedCoherent (W k) := fun k => (hM.truncGE _).truncLT _
  have hW'k : ∀ k, IsLocallyBoundedCoherent (W' k) := fun k => (hM.truncLT _).truncGE _
  -- the cohomology of the windows
  have hWz : ∀ k n, (n < 2 * m k ∨ 2 * m k + 1 < n) → IsZero ((H n).obj (W k)) := by
    intro k n hn
    have : t.IsGE (W k) (2 * m k) :=
      show t.IsGE ((t.truncLT _).obj ((t.truncGE (2 * (k.down : ℤ))).obj M)) _ from inferInstance
    have : t.IsLE (W k) (2 * m k + 1) := t.isLE_truncLT_obj _ _ _ (by simp [m]; omega)
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ (2 * m k) n hn
    · exact DerivedCategory.isZero_of_isLE _ (2 * m k + 1) n hn
  have hW'z : ∀ k n, (n < 2 * m' k ∨ 2 * m' k + 1 < n) → IsZero ((H n).obj (W' k)) := by
    intro k n hn
    have : t.IsGE (W' k) (2 * m' k) := t.isGE_truncGE_obj _ _ _ (by simp [m']; omega)
    have : t.IsLE (W' k) (2 * m' k + 1) :=
      have : t.IsLE ((t.truncLT (-(2 * (k.down : ℤ)))).obj M) (2 * m' k + 1) :=
        t.isLE_truncLT_obj _ _ _ (by simp [m']; omega)
      show t.IsLE ((t.truncGE _).obj ((t.truncLT (-(2 * (k.down : ℤ)))).obj M)) _ from
        inferInstance
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ (2 * m' k) n hn
    · exact DerivedCategory.isZero_of_isLE _ (2 * m' k + 1) n hn
  have hWi : ∀ k (r : ℤ), 0 ≤ r → r ≤ 1 →
      ((H (2 * m k + r)).obj (W k) ≅ (H (2 * m k + r)).obj M) := by
    intro k r h₀ h₁
    have := StacksDraft.ExtremalDegrees.isIso_homology_truncLT (2 * ((k.down + 1 : ℕ) : ℤ))
      (2 * m k + r) (by simp [m]; omega) ((t.truncGE (2 * (k.down : ℤ))).obj M)
    have := StacksDraft.ExtremalDegrees.isIso_homology_truncGE (2 * (k.down : ℤ)) (2 * m k + r)
      (by simp [m]; omega) M
    exact asIso ((H (2 * m k + r)).map ((t.truncLTι _).app _)) ≪≫
      (asIso ((H (2 * m k + r)).map ((t.truncGEπ _).app M))).symm
  have hW'i : ∀ k (r : ℤ), 0 ≤ r → r ≤ 1 →
      ((H (2 * m' k + r)).obj (W' k) ≅ (H (2 * m' k + r)).obj M) := by
    intro k r h₀ h₁
    have := StacksDraft.ExtremalDegrees.isIso_homology_truncGE (-(2 * ((k.down + 1 : ℕ) : ℤ)))
      (2 * m' k + r) (by simp [m']; omega) ((t.truncLT (-(2 * (k.down : ℤ)))).obj M)
    have := StacksDraft.ExtremalDegrees.isIso_homology_truncLT (-(2 * (k.down : ℤ)))
      (2 * m' k + r) (by simp [m']; omega) M
    exact (asIso ((H (2 * m' k + r)).map ((t.truncGEπ _).app _))).symm ≪≫
      asIso ((H (2 * m' k + r)).map ((t.truncLTι _).app M))
  -- the two sums of shifted windows, and their biproduct
  have hsi : ∀ (W : ULift.{u} ℕ → DerivedCategory X.Modules) (m : ULift.{u} ℕ → ℤ) k (n : ℤ),
      (H n).obj ((W k)⟦2 * m k⟧) ≅ (H (2 * m k + n)).obj (W k) := fun W m k n =>
    ((H 0).shiftIso (2 * m k) n _ rfl).app (W k)
  have hsz : ∀ (W : ULift.{u} ℕ → DerivedCategory X.Modules) (m : ULift.{u} ℕ → ℤ),
      (∀ k n, (n < 2 * m k ∨ 2 * m k + 1 < n) → IsZero ((H n).obj (W k))) →
      ∀ k n, (n < 0 ∨ 1 < n) → IsZero ((H n).obj ((W k)⟦2 * m k⟧)) := fun W m hz k n hn =>
    IsZero.of_iso (hz k _ (by omega)) (hsi W m k n)
  have hshift : ∀ (W : ULift.{u} ℕ → DerivedCategory X.Modules) (m : ULift.{u} ℕ → ℤ),
      (∀ k, IsLocallyBoundedCoherent (W k)) → Function.Injective m →
      (∀ k n, (n < 2 * m k ∨ 2 * m k + 1 < n) → IsZero ((H n).obj (W k))) →
      (∀ k n, SheafOfModules.supp ((H n).obj (W k)) ⊆ SheafOfModules.supp ((H n).obj M)) →
      IsLocallyBoundedCoherent (∐ fun k => (W k)⟦2 * m k⟧) := fun W m hWk hm hz hsupp =>
    isLocallyBoundedCoherent_sigma_of_degrees _ (fun k n => ((hWk k).shift _).1 n) {0, 1}
      (fun k n hn => hsz W m hz k n (by simp at hn; omega))
      fun n => (hM.2.comp_injective (f := fun n => SheafOfModules.supp ((H n).obj M))
        (g := fun k => 2 * m k + n) fun a b h => hm (by simp only at h; omega)).subset fun k =>
        (SheafOfModules.supp_eq_of_iso (hsi W m k n)).le.trans (hsupp k _)
  have hV : IsLocallyBoundedCoherent (∐ V) :=
    hshift W m hWk (fun a b h => ULift.ext _ _ (by simp only [m] at h; omega)) hWz
      fun k n => supp_subset_of_isZero_or_iso (homology_truncLT_truncGE M _ _ _)
  have hV' : IsLocallyBoundedCoherent (∐ V') :=
    hshift W' m' hW'k (fun a b h => ULift.ext _ _ (by simp only [m'] at h; omega)) hW'z
      fun k n => supp_subset_of_isZero_or_iso (homology_truncGE_truncLT M _ _ _)
  have hWs : IsLocallyBoundedCoherent (∐ W) :=
    isLocallyBoundedCoherent_sigma_of_isZero_or_iso _ M hM
      (fun k n => homology_truncLT_truncGE M _ _ n)
      fun n => (finite_setOf_two_mul_le n).subset fun k hk => by
        by_contra hlt
        simp only [Set.mem_setOf_eq, not_le] at hlt
        exact hk (hWz k n (Or.inl (by simpa [m] using hlt)))
  have hW's : IsLocallyBoundedCoherent (∐ W') :=
    isLocallyBoundedCoherent_sigma_of_isZero_or_iso _ M hM
      (fun k n => homology_truncGE_truncLT M _ _ n)
      fun n => (finite_setOf_le_neg_two_mul (n + 1)).subset fun k hk => by
        by_contra hlt
        simp only [Set.mem_setOf_eq, not_le] at hlt
        exact hk (hW'z k n (Or.inr (by simp only [m']; push_cast; omega)))
  let Q := (∐ V) ⊞ (∐ V')
  have hQ : IsLocallyBoundedCoherent Q := hV.biprod hV'
  have hQz : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((H n).obj Q) := fun n h₀ h₁ =>
    have := preservesBinaryBiproducts_of_preservesBiproducts
      (DerivedCategory.homologyFunctor X.Modules n)
    IsZero.of_iso ((biprod_isZero_iff _ _).2
      ⟨IsZero.of_iso (isZero_sigma _ fun k => hsz W m hWz k n (by omega))
        (homologyFunctorSigmaIso V n),
       IsZero.of_iso (isZero_sigma _ fun k => hsz W' m' hW'z k n (by omega))
        (homologyFunctorSigmaIso V' n)⟩)
      ((DerivedCategory.homologyFunctor X.Modules n).mapBiprod _ _)
  -- the cohomology of `Q` is the two parity sums of `M`
  have eQ : ∀ r : ℤ, 0 ≤ r → r ≤ 1 → ((H r).obj Q ≅ paritySum M r) := by
    intro r h₀ h₁
    have := preservesBinaryBiproducts_of_preservesBiproducts
      (DerivedCategory.homologyFunctor X.Modules r)
    exact (DerivedCategory.homologyFunctor X.Modules r).mapBiprod _ _ ≪≫
      biprod.mapIso
        (homologyFunctorSigmaIso V r ≪≫
          Limits.Sigma.mapIso fun k => hsi W m k r ≪≫ hWi k r h₀ h₁)
        (homologyFunctorSigmaIso V' r ≪≫
          Limits.Sigma.mapIso fun k => hsi W' m' k r ≪≫ hW'i k r h₀ h₁) ≪≫
      (paritySumSplit M r).symm
  -- the two halves of `Q`
  have : t.IsGE Q 0 := (DerivedCategory.isGE_iff Q 0).2 fun i hi => hQz i (by omega) (by omega)
  have : t.IsLE Q 1 := (DerivedCategory.isLE_iff Q 1).2 fun i hi => hQz i (by omega) (by omega)
  have e₀ : parityEulerClass (Φ.obj ((t.truncLT 1).obj Q)) = parityEulerClass
      (Φ.obj ((DerivedCategory.singleFunctor X.Modules 0).obj (paritySum M 0))) := by
    have : t.IsLE ((t.truncLT 1).obj Q) 0 := t.isLE_truncLT_obj _ _ _ (by norm_num)
    obtain ⟨e⟩ := nonempty_iso_singleFunctor_homology ((t.truncLT 1).obj Q) 0
    have := StacksDraft.ExtremalDegrees.isIso_homology_truncLT 1 0 (by norm_num) Q
    exact parityEulerClass_congr (Φ.mapIso (e ≪≫ (DerivedCategory.singleFunctor X.Modules 0).mapIso
      (asIso ((H 0).map ((t.truncLTι 1).app Q)) ≪≫ eQ 0 le_rfl zero_le_one)))
  have e₁ : parityEulerClass (Φ.obj ((t.truncGE 1).obj Q)) = -parityEulerClass
      (Φ.obj ((DerivedCategory.singleFunctor X.Modules 0).obj (paritySum M 1))) := by
    obtain ⟨e⟩ := nonempty_iso_singleFunctor_homology ((t.truncGE 1).obj Q) 1
    have := StacksDraft.ExtremalDegrees.isIso_homology_truncGE 1 1 le_rfl Q
    have hs : (paritySum M 1).IsCoherent := isCoherent_paritySum hM 1
    rw [parityEulerClass_congr (Φ.mapIso (e ≪≫ (DerivedCategory.singleFunctor X.Modules 1).mapIso
      ((asIso ((H 1).map ((t.truncGEπ 1).app Q))).symm ≪≫ eQ 1 zero_le_one le_rfl))),
      parityEulerClass_congr (StacksDraft.ExtremalDegrees.mapSingleShiftIso Φ (paritySum M 1) 1),
      parityEulerClass_shift_neg_one (hΦ _ (isLocallyBoundedCoherent_single _ hs))]
  -- assembling the steps
  calc parityEulerClass (Φ.obj M)
      = parityEulerClass (Φ.obj ((t.truncLT 0).obj M)) +
          parityEulerClass (Φ.obj ((t.truncGE 0).obj M)) :=
        map_obj₂ Φ hΦ _ (t.triangleLTGE_distinguished 0 M) (hM.truncLT 0) (hM.truncGE 0)
    _ = parityEulerClass (Φ.obj (∐ W')) + parityEulerClass (Φ.obj (∐ W)) :=
        congrArg₂ (· + ·) (map_truncLT_zero Φ hΦ M hM) (map_truncGE_zero Φ hΦ M hM)
    _ = parityEulerClass (Φ.obj (∐ V')) + parityEulerClass (Φ.obj (∐ V)) :=
        congrArg₂ (· + ·) (map_sigma_shift Φ hΦ hΦσ W' m' hW'k hW's hV')
          (map_sigma_shift Φ hΦ hΦσ W m hWk hWs hV)
    _ = parityEulerClass (Φ.obj Q) := by
        rw [add_comm]
        exact (map_biprod Φ hΦ hV hV').symm
    _ = parityEulerClass (Φ.obj ((t.truncLT 1).obj Q)) +
          parityEulerClass (Φ.obj ((t.truncGE 1).obj Q)) :=
        map_obj₂ Φ hΦ _ (t.triangleLTGE_distinguished 1 Q) (hQ.truncLT 1) (hQ.truncGE 1)
    _ = _ := by rw [e₀, e₁, sub_eq_add_neg]

end Devissage


end AlgebraicGeometry.ParityEulerClass
