module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicCokernel

/-!
# Finite biproducts of coherent adic systems on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale ringed site.  This file shows that the category `Coh(F, 𝓘)` of coherent adic systems
of `AlgebraicGeometry.Space.CoherentAdicSystems` has a zero object and finite products, both
computed one level at a time.

The zero object is the constant system on the zero module.  More generally the constant system on
a coherent module annihilated by `𝓘` is a coherent adic system: its transition maps are
identities, and dividing by `𝓘 ^ (n + 1)` changes nothing because that subsheaf already vanishes.

The product of two coherent adic systems is their levelwise biproduct.  Coherence of a biproduct
of coherent modules is `CategoryTheory.ObjectProperty.prop_biprod` together with closure of
coherence under extensions.  The remaining two conditions are checked by splitting a section of a
biproduct as `inl (fst s) + inr (snd s)`, which is `CategoryTheory.Limits.biprod.total` read on
the sections over an étale chart: annihilation of the summands by `𝓘 ^ (n + 1)` then gives
annihilation of the biproduct, and the descent property of the two transition maps gives that of
the biproduct transition, the descents being recombined by `biprod.desc`.

## Main definitions

* `AlgebraicGeometry.Space.biprodSystem` — the levelwise biproduct of two inverse systems of
  `𝒪_F`-modules.
* `AlgebraicGeometry.Space.coherentAdicBiprod` — that biproduct as an object of `Coh(F, 𝓘)`, with
  `AlgebraicGeometry.Space.coherentAdicBiprodBicone` the four structure maps exhibiting it as a
  biproduct.
* `AlgebraicGeometry.Space.coherentAdicZero` — the zero object of `Coh(F, 𝓘)`.

## Main results

* `AlgebraicGeometry.Space.isCoherentAdicSystem_of_exists_desc` — a criterion for an inverse
  system of `𝒪_F`-modules to be a coherent adic system, with the third condition in the form
  "the transition map kills `𝓘 ^ (n + 1)` and every morphism killing it factors through the
  transition map".
* `AlgebraicGeometry.Space.isCoherentAdicSystem_const` — the constant system on a coherent module
  annihilated by `𝓘` is a coherent adic system.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_biprodSystem` — **the levelwise biproduct of two
  coherent adic systems is a coherent adic system.**
* `AlgebraicGeometry.Space.hasZeroObject_coherentAdicSystems` — **`Coh(F, 𝓘)` has a zero
  object.**
* `AlgebraicGeometry.Space.hasBinaryBiproducts_coherentAdicSystems` and
  `AlgebraicGeometry.Space.hasFiniteProducts_coherentAdicSystems` — **`Coh(F, 𝓘)` has binary
  biproducts and all finite products**, and
  `AlgebraicGeometry.Space.hasFiniteBiproducts_coherentAdicSystems` all finite biproducts.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed, as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem`: the term at `n` is the Stacks source's
`E_{n + 1}`, which is why the annihilating exponent at level `n` is `n + 1`.

The biproduct system is built by hand rather than taken as the biproduct of the inverse systems in
the functor category, so that its term at a level is the biproduct of the terms there on the nose
and the three conditions can be checked without transporting along an identification of levelwise
biproducts.  It is then exhibited as a biproduct in `Coh(F, 𝓘)` by
`CategoryTheory.Limits.hasBinaryBiproduct_of_total`, whose hypothesis is exactly the levelwise
`biprod.total`.

Nothing here bears on the existence of kernels in `Coh(F, 𝓘)`, which is not levelwise; that is
`AlgebraicGeometry.Space.hasKernels_coherentAdicSystems`, and the abelian structure of
Stacks 089P (1) built on it is
`AlgebraicGeometry.Space.abelian_coherentAdicSystems` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian`.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### A criterion for being a coherent adic system -/

/-- A criterion for an inverse system of `𝒪_F`-modules to be a coherent adic system, with the
third defining condition replaced by the universal property it expresses: the transition map
annihilates `𝓘 ^ (n + 1)` of its source, and every morphism out of the source which annihilates
that subsheaf factors through the transition map.

A cofork which has that factorization property is a cokernel cofork by
`CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ'`, and the identification of its target with
the chosen cokernel is the isomorphism the third condition asks for. -/
theorem isCoherentAdicSystem_of_exists_desc {Z : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hcoh : ∀ n : ℕ, IsCoherent B S hS F hF (Z.obj (op n)))
    (hann : ∀ n : ℕ, idealPowerMultiple B S hS F hF 𝓘 (n + 1) (Z.obj (op n)) = ⊥)
    (hepi : ∀ n : ℕ, Epi (Z.map (homOfLE (Nat.le_succ n)).op))
    (hw : ∀ n : ℕ, (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (Z.obj (op (n + 1)))).ι ≫
      Z.map (homOfLE (Nat.le_succ n)).op = 0)
    (hdesc : ∀ (n : ℕ) (T : Modules.{u, u} B S hS F hF) (k : Z.obj (op (n + 1)) ⟶ T),
      (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (Z.obj (op (n + 1)))).ι ≫ k = 0 →
      ∃ d : Z.obj (op n) ⟶ T, Z.map (homOfLE (Nat.le_succ n)).op ≫ d = k) :
    IsCoherentAdicSystem B S hS F hF 𝓘 Z := by
  refine ⟨hcoh, hann, fun n => ?_⟩
  have := hepi n
  have hcolim : IsColimit (CokernelCofork.ofπ (Z.map (homOfLE (Nat.le_succ n)).op) (hw n)) :=
    CokernelCofork.IsColimit.ofπ' _ _ fun {T} k hk =>
      ⟨(hdesc n T k hk).choose, (hdesc n T k hk).choose_spec⟩
  exact ⟨IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (Z.obj (op (n + 1)))).ι)
      hcolim,
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (Z.obj (op (n + 1)))).ι)
      hcolim WalkingParallelPair.one⟩

/-! ### The constant system on a module annihilated by `𝓘` -/

/-- The constant inverse system on a coherent `𝒪_F`-module annihilated by `𝓘` is a coherent adic
system.

Every power `𝓘 ^ (n + 1)` already annihilates the module, so each subsheaf `𝓘 ^ (n + 1) M`
vanishes; the transition maps, being identities, therefore kill it, and a morphism out of `M`
factors through the identity as itself. -/
theorem isCoherentAdicSystem_const {M : Modules.{u, u} B S hS F hF}
    (hM : IsCoherent B S hS F hF M) (hann : IsPowAnnihilated B S hS F hF 𝓘 1 M) :
    IsCoherentAdicSystem B S hS F hF 𝓘 ((Functor.const ℕᵒᵖ).obj M) := by
  have hbot : ∀ n : ℕ, idealPowerMultiple B S hS F hF 𝓘 (n + 1) M = ⊥ := fun n =>
    (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) M).mpr fun U r hr x =>
      hann U r (Ideal.pow_le_pow_right (by omega) hr) x
  refine isCoherentAdicSystem_of_exists_desc B S hS F hF 𝓘 (fun _ => hM) (fun n => hbot n)
    (fun _ => inferInstanceAs (Epi (𝟙 M))) (fun n => ?_) fun _ _ k => fun _ => ⟨k, ?_⟩
  · change (idealPowerMultiple B S hS F hF 𝓘 (n + 1) M).ι ≫ 𝟙 M = 0
    rw [Category.comp_id, submodule_ι_eq_zero_of_eq_bot B S hS F hF (hbot n)]
  · change 𝟙 M ≫ k = k
    rw [Category.id_comp]

/-! ### The zero object -/

/-- A section of a zero module on an algebraic space vanishes. -/
theorem eq_zero_of_isZero {M : Modules.{u, u} B S hS F hF} (hM : IsZero M)
    {X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (x : M.val.obj X) : x = 0 :=
  congrArg (fun k : M ⟶ M => k.val.app X x) ((IsZero.iff_id_eq_zero M).mp hM)

/-- The constant system on the zero module is a coherent adic system. -/
theorem isCoherentAdicSystem_zero :
    IsCoherentAdicSystem B S hS F hF 𝓘
      ((Functor.const ℕᵒᵖ).obj (0 : Modules.{u, u} B S hS F hF)) :=
  isCoherentAdicSystem_const B S hS F hF 𝓘
    (IsCoherent.of_isZero B S hS F hF (isZero_zero _)) fun _ _ _ x => by
      rw [eq_zero_of_isZero B S hS F hF (isZero_zero _) x, smul_zero]

/-- The zero object of `Coh(F, 𝓘)`: the constant system on the zero `𝒪_F`-module. -/
def coherentAdicZero : CoherentAdicSystems B S hS F hF 𝓘 :=
  ⟨(Functor.const ℕᵒᵖ).obj (0 : Modules.{u, u} B S hS F hF),
    isCoherentAdicSystem_zero B S hS F hF 𝓘⟩

/-- `AlgebraicGeometry.Space.coherentAdicZero` is a zero object: it is one in the ambient category
of inverse systems, since all of its terms are, and the inclusion of a full subcategory is
faithful. -/
theorem isZero_coherentAdicZero : IsZero (coherentAdicZero B S hS F hF 𝓘) := by
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) ?_
  exact (Functor.isZero _ fun _ => isZero_zero _).eq_of_src _ _

/-- **The category `Coh(F, 𝓘)` of coherent adic systems on an algebraic space has a zero
object.** -/
instance hasZeroObject_coherentAdicSystems :
    HasZeroObject (CoherentAdicSystems B S hS F hF 𝓘) :=
  (isZero_coherentAdicZero B S hS F hF 𝓘).hasZeroObject

/-! ### Sections of a biproduct -/

/-- A section of a biproduct of `𝒪_F`-modules over an étale chart is the sum of the images of its
two components.  This is `CategoryTheory.Limits.biprod.total` read on sections. -/
theorem biprod_inl_fst_add_inr_snd (X Y : Modules.{u, u} B S hS F hF)
    {W : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (s : (X ⊞ Y).val.obj W) :
    (biprod.inl : X ⟶ X ⊞ Y).val.app W ((biprod.fst : X ⊞ Y ⟶ X).val.app W s)
      + (biprod.inr : Y ⟶ X ⊞ Y).val.app W ((biprod.snd : X ⊞ Y ⟶ Y).val.app W s) = s :=
  congrArg (fun k : (X ⊞ Y) ⟶ (X ⊞ Y) => k.val.app W s) (biprod.total (X := X) (Y := Y))

/-- A map out of a biproduct of `𝒪_F`-modules kills `r • s` for every section `s` as soon as it
kills `r • x` after each of the two inclusions. -/
private theorem biprod_app_smul_eq_zero {X Y T : Modules.{u, u} B S hS F hF}
    (g : X ⊞ Y ⟶ T) {U : SmallEtale B S hS F} (r : chartRing B S hS F hF U)
    (hl : ∀ x : X.val.obj (op U), g.val.app (op U) ((biprod.inl : X ⟶ X ⊞ Y).val.app (op U) (r • x))
      = 0)
    (hr : ∀ y : Y.val.obj (op U), g.val.app (op U) ((biprod.inr : Y ⟶ X ⊞ Y).val.app (op U) (r • y))
      = 0)
    (s : (X ⊞ Y).val.obj (op U)) : g.val.app (op U) (r • s) = 0 := by
  rw [← biprod_inl_fst_add_inr_snd B S hS F hF X Y s, smul_add,
    ← ((biprod.inl : X ⟶ X ⊞ Y).val.app (op U)).hom.map_smul r _,
    ← ((biprod.inr : Y ⟶ X ⊞ Y).val.app (op U)).hom.map_smul r _, map_add, hl, hr, add_zero]

/-- A biproduct of two `𝒪_F`-modules annihilated by `𝓘 ^ k` is annihilated by `𝓘 ^ k`: a section
of the biproduct splits into its two components, each of which is killed. -/
theorem isPowAnnihilated_biprod (k : ℕ) (X Y : Modules.{u, u} B S hS F hF)
    (hX : IsPowAnnihilated B S hS F hF 𝓘 k X) (hY : IsPowAnnihilated B S hS F hF 𝓘 k Y) :
    IsPowAnnihilated B S hS F hF 𝓘 k (X ⊞ Y) := fun U r hr s =>
  biprod_app_smul_eq_zero B S hS F hF (𝟙 (X ⊞ Y)) r
    (fun x => by rw [hX U r hr x, map_zero, map_zero])
    (fun y => by rw [hY U r hr y, map_zero, map_zero]) s

/-! ### The levelwise biproduct of two inverse systems -/

/-- The levelwise biproduct of two inverse systems of `𝒪_F`-modules. -/
def biprodSystem (X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF where
  obj n := X.obj n ⊞ Y.obj n
  map g := biprod.map (X.map g) (Y.map g)
  map_id n := by
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [biprod.map_fst, X.map_id, Category.comp_id, Category.id_comp]
    · rw [biprod.map_snd, Y.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The transition map of a levelwise biproduct is the biproduct of the transition maps. -/
theorem biprodSystem_map (X Y : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (biprodSystem B S hS F hF X Y).map g = biprod.map (X.map g) (Y.map g) :=
  rfl

section Biprod

variable {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-- The transition map of the levelwise biproduct of two coherent adic systems annihilates
`𝓘 ^ (n + 1)` of its source: a section of the biproduct splits into its two components, and the
transition map of each system kills `𝓘 ^ (n + 1)` of the term it comes from. -/
theorem idealPowerMultiple_ι_comp_biprodSystem_map_eq_zero (n : ℕ) :
    (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      ((biprodSystem B S hS F hF E.obj E'.obj).obj (op (n + 1)))).ι ≫
        (biprodSystem B S hS F hF E.obj E'.obj).map (homOfLE (Nat.le_succ n)).op = 0 := by
  have hE := (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 (n + 1)
    (E.obj.map (homOfLE (Nat.le_succ n)).op)).mp
      (idealPowerMultiple_ι_comp_map_succ_eq_zero B S hS F hF 𝓘 E.property n)
  have hE' := (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 (n + 1)
    (E'.obj.map (homOfLE (Nat.le_succ n)).op)).mp
      (idealPowerMultiple_ι_comp_map_succ_eq_zero B S hS F hF 𝓘 E'.property n)
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 (n + 1) _).mpr fun U r hr s => ?_
  set A := E.obj.obj (op (n + 1))
  set A' := E'.obj.obj (op (n + 1))
  set f := E.obj.map (homOfLE (Nat.le_succ n)).op
  set f' := E'.obj.map (homOfLE (Nat.le_succ n)).op
  change (biprod.map f f').val.app (op U) (r • s) = 0
  refine biprod_app_smul_eq_zero B S hS F hF _ r (fun x => ?_) (fun y => ?_) s
  · change (biprod.inl ≫ biprod.map f f').val.app (op U) (r • x) = 0
    rw [biprod.inl_map]
    change (biprod.inl : E.obj.obj (op n) ⟶ _).val.app (op U) (f.val.app (op U) (r • x)) = 0
    rw [hE U r hr x, map_zero]
  · change (biprod.inr ≫ biprod.map f f').val.app (op U) (r • y) = 0
    rw [biprod.inr_map]
    change (biprod.inr : E'.obj.obj (op n) ⟶ _).val.app (op U) (f'.val.app (op U) (r • y)) = 0
    rw [hE' U r hr y, map_zero]

/-- A morphism out of the term at level `n + 1` of the levelwise biproduct of two coherent adic
systems which annihilates `𝓘 ^ (n + 1)` of that term factors through the transition map.

Its restrictions along the two inclusions annihilate `𝓘 ^ (n + 1)` of the respective summands, so
each descends along the transition map of that system; the two descents are recombined by
`CategoryTheory.Limits.biprod.desc`. -/
theorem exists_desc_of_biprodSystem_map_succ (n : ℕ) {T : Modules.{u, u} B S hS F hF}
    (k : (biprodSystem B S hS F hF E.obj E'.obj).obj (op (n + 1)) ⟶ T)
    (hk : (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      ((biprodSystem B S hS F hF E.obj E'.obj).obj (op (n + 1)))).ι ≫ k = 0) :
    ∃ d : (biprodSystem B S hS F hF E.obj E'.obj).obj (op n) ⟶ T,
      (biprodSystem B S hS F hF E.obj E'.obj).map (homOfLE (Nat.le_succ n)).op ≫ d = k := by
  obtain ⟨dE, hdE⟩ := exists_desc_of_transition B S hS F hF 𝓘 E.property n (biprod.inl ≫ k)
    (idealPowerMultiple_ι_comp_comp_eq_zero B S hS F hF 𝓘 (n + 1) biprod.inl k hk)
  obtain ⟨dE', hdE'⟩ := exists_desc_of_transition B S hS F hF 𝓘 E'.property n (biprod.inr ≫ k)
    (idealPowerMultiple_ι_comp_comp_eq_zero B S hS F hF 𝓘 (n + 1) biprod.inr k hk)
  have hmap : biprod.map (E.obj.map (homOfLE (Nat.le_succ n)).op)
      (E'.obj.map (homOfLE (Nat.le_succ n)).op) ≫ biprod.desc dE dE' = k := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc, hdE]
    · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc, hdE']
  exact ⟨biprod.desc dE dE', hmap⟩

/-- **The levelwise biproduct of two coherent adic systems is a coherent adic system.** -/
theorem isCoherentAdicSystem_biprodSystem :
    IsCoherentAdicSystem B S hS F hF 𝓘 (biprodSystem B S hS F hF E.obj E'.obj) :=
  isCoherentAdicSystem_of_exists_desc B S hS F hF 𝓘
    (fun n => (isCoherent.{u, u} B S hS F hF).prop_biprod (E.property.1 n) (E'.property.1 n))
    (fun n => (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mpr
      (isPowAnnihilated_biprod B S hS F hF 𝓘 (n + 1) _ _
        ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mp (E.property.2.1 n))
        ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mp (E'.property.2.1 n))))
    (fun n =>
      have := epi_map_le_succ B S hS F hF 𝓘 E.property n
      have := epi_map_le_succ B S hS F hF 𝓘 E'.property n
      inferInstanceAs (Epi (biprod.map (E.obj.map (homOfLE (Nat.le_succ n)).op)
        (E'.obj.map (homOfLE (Nat.le_succ n)).op))))
    (fun n => idealPowerMultiple_ι_comp_biprodSystem_map_eq_zero B S hS F hF 𝓘 n)
    fun n _ k hk => exists_desc_of_biprodSystem_map_succ B S hS F hF 𝓘 n k hk

/-- The levelwise biproduct of two coherent adic systems, as an object of `Coh(F, 𝓘)`. -/
def coherentAdicBiprod (E E' : CoherentAdicSystems B S hS F hF 𝓘) :
    CoherentAdicSystems B S hS F hF 𝓘 :=
  ⟨biprodSystem B S hS F hF E.obj E'.obj, isCoherentAdicSystem_biprodSystem B S hS F hF 𝓘⟩

/-- The four structure maps exhibiting `AlgebraicGeometry.Space.coherentAdicBiprod` as a
biproduct in `Coh(F, 𝓘)`.  Each is levelwise one of the structure maps of the biproduct of the
terms, and the four relations hold level by level. -/
def coherentAdicBiprodBicone (E E' : CoherentAdicSystems B S hS F hF 𝓘) :
    BinaryBicone E E' where
  pt := coherentAdicBiprod B S hS F hF 𝓘 E E'
  fst := ObjectProperty.homMk
    { app := fun _ => biprod.fst
      naturality := fun _ _ g => biprod.map_fst (E.obj.map g) (E'.obj.map g) }
  snd := ObjectProperty.homMk
    { app := fun _ => biprod.snd
      naturality := fun _ _ g => biprod.map_snd (E.obj.map g) (E'.obj.map g) }
  inl := ObjectProperty.homMk
    { app := fun _ => biprod.inl
      naturality := fun _ _ g => (biprod.inl_map (E.obj.map g) (E'.obj.map g)).symm }
  inr := ObjectProperty.homMk
    { app := fun _ => biprod.inr
      naturality := fun _ _ g => (biprod.inr_map (E.obj.map g) (E'.obj.map g)).symm }
  inl_fst := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => biprod.inl_fst))
  inl_snd := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => biprod.inl_snd))
  inr_fst := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => biprod.inr_fst))
  inr_snd := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => biprod.inr_snd))

/-- The structure maps of `AlgebraicGeometry.Space.coherentAdicBiprodBicone` satisfy the identity
which makes a bicone in a preadditive category a biproduct, because they do so level by level. -/
theorem coherentAdicBiprodBicone_total (E E' : CoherentAdicSystems B S hS F hF 𝓘) :
    (coherentAdicBiprodBicone B S hS F hF 𝓘 E E').fst ≫
        (coherentAdicBiprodBicone B S hS F hF 𝓘 E E').inl +
      (coherentAdicBiprodBicone B S hS F hF 𝓘 E E').snd ≫
        (coherentAdicBiprodBicone B S hS F hF 𝓘 E E').inr =
      𝟙 (coherentAdicBiprodBicone B S hS F hF 𝓘 E E').pt :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => biprod.total))

end Biprod

/-- **Two coherent adic systems have a biproduct in `Coh(F, 𝓘)`**, namely their levelwise
biproduct. -/
instance hasBinaryBiproduct_coherentAdicSystems (E E' : CoherentAdicSystems B S hS F hF 𝓘) :
    HasBinaryBiproduct E E' :=
  hasBinaryBiproduct_of_total (coherentAdicBiprodBicone B S hS F hF 𝓘 E E')
    (coherentAdicBiprodBicone_total B S hS F hF 𝓘 E E')

/-- **`Coh(F, 𝓘)` has binary biproducts.** -/
instance hasBinaryBiproducts_coherentAdicSystems :
    HasBinaryBiproducts (CoherentAdicSystems B S hS F hF 𝓘) where
  has_binary_biproduct E E' := hasBinaryBiproduct_coherentAdicSystems B S hS F hF 𝓘 E E'

/-- **`Coh(F, 𝓘)` has all finite products.**  It has binary products, those being the levelwise
biproducts, and a terminal object, namely its zero object. -/
instance hasFiniteProducts_coherentAdicSystems :
    HasFiniteProducts (CoherentAdicSystems B S hS F hF 𝓘) :=
  haveI : HasBinaryProducts (CoherentAdicSystems B S hS F hF 𝓘) :=
    hasBinaryProducts_of_hasBinaryBiproducts
  haveI : HasTerminal (CoherentAdicSystems B S hS F hF 𝓘) :=
    (isZero_zero (CoherentAdicSystems B S hS F hF 𝓘)).isTerminal.hasTerminal
  hasFiniteProducts_of_has_binary_and_terminal

/-- **`Coh(F, 𝓘)` has all finite biproducts.** -/
instance hasFiniteBiproducts_coherentAdicSystems :
    HasFiniteBiproducts (CoherentAdicSystems B S hS F hF 𝓘) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end AlgebraicGeometry.Space

end
