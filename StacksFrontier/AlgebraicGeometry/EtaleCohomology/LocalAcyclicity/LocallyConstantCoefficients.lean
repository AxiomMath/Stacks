module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.Basic
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Local acyclicity with locally constant torsion coefficients

Let `f : X ⟶ S` be a morphism of schemes and let `F` be a locally constant abelian sheaf on
`X_étale` whose geometric stalks are torsion with all element orders prime to the residue
characteristic. Tag 0GJR says that if `f` is locally acyclic then `f` is locally acyclic relative
to `F`.

The source argues at a geometric point `x`: the restriction of `F` to `Spec 𝒪^{sh}_{X,x}` is the
constant sheaf with value `M = F_x`; `M` is a filtered colimit of finite subgroups `M_i` whose
element orders are prime to the residue characteristic; each `M_i` is a finite direct sum of
cyclic groups `ℤ/n_{i,j}ℤ`; local acyclicity of `f` evaluates the canonical map on each cyclic
summand; and the direct sums and the colimit are reassembled.

This file proves that reassembly — the dévissage — and takes the two facts about the strict
henselization as hypotheses. The split is the one in the source's own proof: everything that
happens to the *coefficient group* is proved here, and everything that happens to the *strict
henselization* is assumed.

## Main results

* `Stacks.TorsionDevissage.exists_isColimit_finite_of_torsion` — a torsion abelian group is the
  filtered colimit of its finite subgroups, and the prime-to-`p` condition on element orders is
  inherited by every member of the system.
* `Stacks.TorsionDevissage.isIso_app_of_iso` and `Stacks.TorsionDevissage.isIso_app_biprod` —
  the locus where a natural transformation between additive functors out of abelian groups is an
  isomorphism is invariant under isomorphism and closed under binary biproducts.
* `Stacks.TorsionDevissage.isIso_app_of_finite` — that locus contains every finite abelian group
  of prime-to-`p` element order as soon as it contains the cyclic groups `ℤ/nℤ` with `n` prime
  to `p`.
* `Stacks.TorsionDevissage.isIso_app_of_torsion` — the full dévissage: the locus contains every
  prime-to-`p` torsion abelian group, provided it is closed under filtered colimits.
* `AlgebraicGeometry.isLocallyAcyclicRelative_of_isLocallyConstant` — **[Stacks, Tag 0GJR]** the
  dévissage applied to the canonical map of Tag 0GJN.

## The hypotheses carried by the main theorem

`hdep` and `hconst` are the two inputs about the strict henselization. Each is a statement in its
own right about `Spec 𝒪^{sh}_{X,x}`, and neither mentions the conclusion:

* `hdep` says the canonical map `α_{K,x,t}` has the same iso-status at two objects of
  `D(X_étale)` whose inverse images on `Spec 𝒪^{sh}_{X,x}` agree. This is what the identification
  `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)` buys: source and target of `α` are both computed from that
  inverse image.
* `hconst` says the inverse image of a locally constant sheaf on `Spec 𝒪^{sh}_{X,x}` is the
  constant sheaf with value its stalk at `x`, because `Spec 𝒪^{sh}_{X,x}` is strictly henselian
  local, so the covering trivialising the sheaf splits.

`hcolim` is Tag 03Q5 in the form the argument uses it. It is not phrased as "`α` preserves
filtered colimits": `D(X_étale)` has no filtered colimits of the relevant diagrams, and the
source uses none — it uses that cohomology of the affine variety of vanishing cycles commutes
with filtered colimits of the *coefficient group*, which is closure of the iso-locus.

`hadd` is additivity of unbounded derived global sections on each variety of vanishing cycles. It
is purely formal, `RΓ` being the total right derived functor of the additive `Sheaf.Γ`, but
Mathlib registers no `Functor.Additive` instance for `Functor.totalRightDerived`, so it is
supplied rather than synthesised.

## References

* [Stacks Project, Tag 0GJR](https://stacks.math.columbia.edu/tag/0GJR)
* [Stacks Project, Tag 0GJP](https://stacks.math.columbia.edu/tag/0GJP)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.TorsionDevissage

/-! ### A torsion abelian group is the filtered colimit of its finite subgroups -/

/-- The supremum of two finite subgroups of an additive commutative group is again finite:
every element of `K ⊔ K'` is a sum of an element of `K` and an element of `K'`. -/
instance finite_sup {G : Type*} [AddCommGroup G] (K K' : AddSubgroup G)
    [Finite K] [Finite K'] : Finite (↥(K ⊔ K')) := by
  refine Finite.of_surjective (fun q : K × K' => (⟨(q.1 : G) + (q.2 : G),
    AddSubgroup.mem_sup.2 ⟨q.1, q.1.2, q.2, q.2.2, rfl⟩⟩ : ↥(K ⊔ K'))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hx
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

/-- The poset of finite subgroups of an object `M` of `AddCommGrpCat`, ordered by inclusion. -/
abbrev FinSubgroup (M : AddCommGrpCat.{w}) : Type w := {K : AddSubgroup (M : Type w) // Finite K}

/-- The trivial subgroup witnesses that `FinSubgroup M` is nonempty. -/
instance FinSubgroup.instNonempty (M : AddCommGrpCat.{w}) : Nonempty (FinSubgroup M) :=
  ⟨⟨⊥, inferInstance⟩⟩

/-- Finite subgroups of `M` are directed by inclusion, since `K ⊔ K'` is again finite. -/
instance FinSubgroup.instIsDirectedOrder (M : AddCommGrpCat.{w}) :
    IsDirectedOrder (FinSubgroup M) := by
  refine ⟨fun K K' => ⟨⟨K.1 ⊔ K'.1, have := K.2; have := K'.2; inferInstance⟩, ?_, ?_⟩⟩
  · exact (le_sup_left : K.1 ≤ K.1 ⊔ K'.1)
  · exact (le_sup_right : K'.1 ≤ K.1 ⊔ K'.1)

/-- The diagram of all finite subgroups of `M`, with the inclusions as transition maps. -/
def finSubgroupDiagram (M : AddCommGrpCat.{w}) : FinSubgroup M ⥤ AddCommGrpCat.{w} where
  obj K := AddCommGrpCat.of K.1
  map {_ _} h := AddCommGrpCat.ofHom (AddSubgroup.inclusion (leOfHom h))

/-- The cocone on `finSubgroupDiagram M` whose point is `M` and whose legs are the subgroup
inclusions. -/
def finSubgroupCocone (M : AddCommGrpCat.{w}) : Cocone (finSubgroupDiagram M) where
  pt := M
  ι := { app := fun K => AddCommGrpCat.ofHom K.1.subtype }

/-- A torsion abelian group is the filtered colimit of its finite subgroups, and when every
element has order prime to `p` the same holds of every element of every member of the system. -/
theorem exists_isColimit_finite_of_torsion {p : ℕ} (M : AddCommGrpCat.{w})
    (hM : ∀ a : M, ∃ n : ℕ, 0 < n ∧ (p = 0 ∨ Nat.Coprime n p) ∧ n • a = 0) :
    ∃ (I : Type w) (_ : SmallCategory I) (_ : IsFiltered I) (N : I ⥤ AddCommGrpCat.{w})
      (c : Cocone N) (_ : IsColimit c), Nonempty (c.pt ≅ M) ∧
      ∀ i, Finite (N.obj i) ∧
        ∀ a : N.obj i, ∃ n : ℕ, 0 < n ∧ (p = 0 ∨ Nat.Coprime n p) ∧ n • a = 0 := by
  refine ⟨FinSubgroup M, inferInstance, inferInstance, finSubgroupDiagram M,
    finSubgroupCocone M, ?_, ⟨Iso.refl _⟩, ?_⟩
  · have := reflectsColimit_of_reflectsIsomorphisms (finSubgroupDiagram M)
      (forget AddCommGrpCat.{w})
    refine isColimitOfReflects (forget AddCommGrpCat.{w}) ?_
    refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
    · intro a
      refine ⟨⟨AddSubgroup.zmultiples (@id (M : Type w) a), ?_⟩,
        ⟨@id (M : Type w) a, AddSubgroup.mem_zmultiples _⟩, rfl⟩
      obtain ⟨n, hn, -, hna⟩ := hM a
      exact (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hna⟩).finite_zmultiples.to_subtype
    · intro K K' x y h
      obtain ⟨L, hKL, hK'L⟩ := exists_ge_ge K K'
      exact ⟨L, homOfLE hKL, homOfLE hK'L, Subtype.ext h⟩
  · intro K
    refine ⟨K.2, fun a => ?_⟩
    obtain ⟨n, hn, hp, hna⟩ := hM (Subtype.val (p := fun x => x ∈ K.1) a)
    exact ⟨n, hn, hp, Subtype.ext hna⟩

/-! ### The locus where a natural transformation on abelian coefficients is an isomorphism -/

section Locus

variable {𝒟 : Type*} [Category 𝒟] {G H : AddCommGrpCat.{w} ⥤ 𝒟} (η : G ⟶ H)

/-- The locus where a natural transformation is an isomorphism is invariant under isomorphism of
the object it is evaluated at. -/
theorem isIso_app_of_iso {A B : AddCommGrpCat.{w}} (e : A ≅ B) (h : IsIso (η.app A)) :
    IsIso (η.app B) := by
  have key : η.app B = inv (G.map e.hom) ≫ η.app A ≫ H.map e.hom := by
    rw [← η.naturality e.hom, IsIso.inv_hom_id_assoc]
  rw [key]
  infer_instance

variable [Preadditive 𝒟] [HasBinaryBiproducts 𝒟] [G.Additive] [H.Additive]

/-- The locus where a natural transformation between additive functors is an isomorphism is
closed under binary biproducts. -/
theorem isIso_app_biprod {A B : AddCommGrpCat.{w}} (hA : IsIso (η.app A))
    (hB : IsIso (η.app B)) : IsIso (η.app (A ⊞ B)) := by
  have _hG : HasBinaryBiproduct (G.obj A) (G.obj B) := inferInstance
  have _hH : HasBinaryBiproduct (H.obj A) (H.obj B) := inferInstance
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have sq : η.app (A ⊞ B) ≫ (H.mapBiprod A B).hom
      = (G.mapBiprod A B).hom ≫ biprod.map (η.app A) (η.app B) := by
    apply biprod.hom_ext
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc]
      exact (η.naturality (biprod.fst : A ⊞ B ⟶ A)).symm
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc]
      exact (η.naturality (biprod.snd : A ⊞ B ⟶ B)).symm
  have hmap : IsIso (biprod.map (η.app A) (η.app B)) :=
    inferInstanceAs (IsIso (biprod.mapIso (asIso (η.app A)) (asIso (η.app B))).hom)
  have key : η.app (A ⊞ B)
      = ((G.mapBiprod A B).hom ≫ biprod.map (η.app A) (η.app B)) ≫ (H.mapBiprod A B).inv :=
    (Iso.eq_comp_inv _).2 sq
  rw [key]
  infer_instance

/-- Any two trivial additive commutative groups are additively isomorphic. -/
def subsingletonAddEquiv (X Y : Type*) [AddCommGroup X] [AddCommGroup Y] [Subsingleton X]
    [Subsingleton Y] : X ≃+ Y where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := (add_zero (0 : Y)).symm

/-- The `ULift` of a product of additive groups is the product of their `ULift`s. -/
def uliftProdAddEquiv (X Y : Type) [AddCommGroup X] [AddCommGroup Y] :
    ULift.{w} (X × Y) ≃+ ULift.{w} X × ULift.{w} Y where
  toFun x := (⟨x.down.1⟩, ⟨x.down.2⟩)
  invFun x := ⟨(x.1.down, x.2.down)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Reindexing a product of additive groups along an equivalence of index types. -/
def piCongrLeftAddEquiv {α β : Type*} (Z : α → Type*) [∀ a, AddCommGroup (Z a)] (e : α ≃ β) :
    (∀ a, Z a) ≃+ ∀ b, Z (e.symm b) :=
  AddEquiv.mk' (Equiv.piCongrLeft' Z e) fun _ _ => rfl

/-- Splitting off the zeroth factor of a finite product of groups indexed by `Fin (n + 1)`. -/
def piFinSuccAddEquiv (n : ℕ) (B : Fin (n + 1) → Type*) [∀ j, AddCommGroup (B j)] :
    B 0 × (∀ j : Fin n, B j.succ) ≃+ ∀ j : Fin (n + 1), B j where
  toFun x := Fin.cases x.1 x.2
  invFun g := (g 0, fun j => g j.succ)
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp
    · funext j; simp
  right_inv g := by
    funext j
    refine Fin.cases ?_ ?_ j <;> intros <;> simp
  map_add' x y := by
    funext j
    refine Fin.cases ?_ ?_ j <;> intros <;> simp

/-- A product of two `ULift`ed groups, bundled in `AddCommGrpCat`, is their binary biproduct. -/
def uliftProdBiprodIso (X Y : Type) [AddCommGroup X] [AddCommGroup Y] :
    (AddCommGrpCat.of (ULift.{w} X) ⊞ AddCommGrpCat.of (ULift.{w} Y)) ≅
      AddCommGrpCat.of (ULift.{w} (X × Y)) :=
  AddCommGrpCat.biprodIsoProd _ _ ≪≫ (uliftProdAddEquiv X Y).symm.toAddCommGrpIso

/-- The iso-locus contains every finite product of cyclic groups of prime-to-`p` order. -/
theorem isIso_app_piFin {p : ℕ}
    (hzmod : ∀ n : ℕ, 0 < n → (p = 0 ∨ Nat.Coprime n p) →
      IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod n))))) :
    ∀ (n : ℕ) (q : Fin n → ℕ), (∀ j, 0 < q j) → (∀ j, p = 0 ∨ Nat.Coprime (q j) p) →
      IsIso (η.app (AddCommGrpCat.of (ULift.{w} (∀ j : Fin n, ZMod (q j))))) := by
  intro n
  induction n with
  | zero =>
      intro q _ _
      refine isIso_app_of_iso η ?_ (hzmod 1 Nat.one_pos (Or.inr (Nat.coprime_one_left p)))
      exact (subsingletonAddEquiv (ULift.{w} (ZMod 1))
        (ULift.{w} (∀ j : Fin 0, ZMod (q j)))).toAddCommGrpIso
  | succ n ih =>
      intro q hq hc
      have h0 : IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod (q 0))))) :=
        hzmod (q 0) (hq 0) (hc 0)
      have htail : IsIso (η.app (AddCommGrpCat.of
          (ULift.{w} (∀ j : Fin n, ZMod (q j.succ))))) :=
        ih (fun j => q j.succ) (fun j => hq _) (fun j => hc _)
      refine isIso_app_of_iso η ?_ (isIso_app_biprod η h0 htail)
      refine uliftProdBiprodIso _ _ ≪≫ ?_
      exact (AddEquiv.ulift.trans
        ((piFinSuccAddEquiv n (fun j => ZMod (q j))).trans AddEquiv.ulift.symm)).toAddCommGrpIso

/-- The iso-locus contains every finite abelian group all of whose elements have order prime to
`p`, as soon as it contains the cyclic groups of prime-to-`p` order. -/
theorem isIso_app_of_finite {p : ℕ}
    (hzmod : ∀ n : ℕ, 0 < n → (p = 0 ∨ Nat.Coprime n p) →
      IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod n)))))
    (A : AddCommGrpCat.{w}) [Finite A]
    (hA : ∀ a : A, ∃ n : ℕ, 0 < n ∧ (p = 0 ∨ Nat.Coprime n p) ∧ n • a = 0) :
    IsIso (η.app A) := by
  classical
  obtain ⟨ι, _, m, hm, ⟨f0⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (A : Type w)
  have f : (A : Type w) ≃+ ∀ i, ZMod (m i) := f0.trans (DirectSum.addEquivProd _)
  have hcop : ∀ i, p = 0 ∨ Nat.Coprime (m i) p := by
    intro i
    obtain ⟨n, _, hnp, hna⟩ :=
      hA (f.symm (Pi.single (M := fun i => ZMod (m i)) i (1 : ZMod (m i))))
    rcases hnp with h | h
    · exact Or.inl h
    · refine Or.inr (Nat.Coprime.coprime_dvd_left ?_ h)
      have hns : n • (Pi.single (M := fun i => ZMod (m i)) i (1 : ZMod (m i))) = 0 := by
        have h2 := congrArg f hna
        rw [map_nsmul, map_zero, AddEquiv.apply_symm_apply] at h2
        exact h2
      have h1 : n • (1 : ZMod (m i)) = 0 := by
        have h3 := congrFun hns i
        simpa using h3
      have h4 := addOrderOf_dvd_of_nsmul_eq_zero h1
      rwa [ZMod.addOrderOf_one] at h4
  have key : IsIso (η.app (AddCommGrpCat.of
      (ULift.{w} (∀ j : Fin (Fintype.card ι), ZMod (m ((Fintype.equivFin ι).symm j)))))) :=
    isIso_app_piFin η hzmod _ _ (fun j => lt_trans Nat.one_pos (hm _)) (fun j => hcop _)
  refine isIso_app_of_iso η ?_ key
  exact (AddEquiv.ulift.trans
    ((piCongrLeftAddEquiv (fun i => ZMod (m i)) (Fintype.equivFin ι)).symm.trans
      f.symm)).toAddCommGrpIso

/-- **The dévissage.** If the locus where a natural transformation between additive functors on
abelian groups is an isomorphism contains the cyclic groups `ℤ/nℤ` of prime-to-`p` order and is
closed under filtered colimits, then it contains every torsion abelian group all of whose
elements have order prime to `p`.

This is the combinatorial half of Tag 0GJR: the group `M` is the filtered colimit of its finite
subgroups, and each of those splits as a finite direct sum of cyclic groups of prime-to-`p`
order. -/
theorem isIso_app_of_torsion {p : ℕ}
    (hcolim : ∀ {I : Type w} [SmallCategory I] [IsFiltered I] (N : I ⥤ AddCommGrpCat.{w})
      (c : Cocone N), IsColimit c → (∀ i, IsIso (η.app (N.obj i))) → IsIso (η.app c.pt))
    (hzmod : ∀ n : ℕ, 0 < n → (p = 0 ∨ Nat.Coprime n p) →
      IsIso (η.app (AddCommGrpCat.of (ULift.{w} (ZMod n)))))
    (M : AddCommGrpCat.{w})
    (hM : ∀ a : M, ∃ n : ℕ, 0 < n ∧ (p = 0 ∨ Nat.Coprime n p) ∧ n • a = 0) :
    IsIso (η.app M) := by
  obtain ⟨I, _, _, N, c, hc, ⟨e⟩, hfin⟩ := exists_isColimit_finite_of_torsion (p := p) M hM
  refine isIso_app_of_iso η e ?_
  refine hcolim N c hc fun i => ?_
  have := (hfin i).1
  exact isIso_app_of_finite η hzmod (N.obj i) (hfin i).2

end Locus

end Stacks.TorsionDevissage

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Constant coefficients as a functor: the abelian group `M` goes to the constant sheaf with
value `M` on the small étale site of `X`, placed in degree zero of `D(X_étale)`.

On objects this is `Stacks.EtaleCohomology.smallEtaleConstantComplexAb`. -/
def smallEtaleConstantComplexFunctor (X : Scheme.{u}) : Ab.{u + 1} ⥤ smallEtaleDerivedCategory X :=
  constantSheaf X.smallEtaleTopology Ab.{u + 1} ⋙
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0

/-- Constant coefficients form an additive functor: the constant sheaf functor is a left adjoint
and the degree-zero inclusion of a sheaf into the derived category is additive. -/
instance smallEtaleConstantComplexFunctor_additive (X : Scheme.{u}) :
    (smallEtaleConstantComplexFunctor X).Additive := by
  unfold smallEtaleConstantComplexFunctor; infer_instance

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology Stacks.TorsionDevissage

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0GJR.** Let `f : X ⟶ S` be a morphism of schemes and let `F` be a locally constant
abelian sheaf on `X_étale` whose stalk at every geometric point `x` is torsion with every element
order prime to the characteristic of the residue field at `x`. If `f` is locally acyclic, then
`f` is locally acyclic relative to `F`.

What is proved here is the dévissage: the reduction of the locally constant torsion coefficient
sheaf `F` to the constant sheaves `ℤ/nℤ` that local acyclicity speaks about. The stalk is written
as the filtered colimit of its finite subgroups, each of those splits as a finite direct sum of
cyclic groups of prime-to-`p` order, and local acyclicity is applied to each summand.

Four hypotheses are supplied rather than derived.

* `hdep` and `hconst` are the two facts about the strict henselization that the source's proof
  rests on, each stated in its own right. `hdep` is the consequence of
  `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)` that the canonical map only sees the inverse image of `K` on
  `Spec 𝒪^{sh}_{X,x}`; `hconst` is that a locally constant sheaf has constant inverse image
  there, with value its stalk.
* `hcolim` is Tag 03Q5 for the affine variety of vanishing cycles, in the form the argument
  consumes it: the iso-locus of the canonical map on constant coefficients is closed under
  filtered colimits of the coefficient group.
* `hadd` is additivity of unbounded derived global sections, which is formal but not an
  available instance.

See the module docstring for why `hcolim` cannot be stated as preservation of filtered
colimits. -/
@[stacks 0GJR "the dévissage from constant ℤ/nℤ coefficients to a locally constant \
prime-to-residue-characteristic torsion sheaf: the stalk is the filtered colimit of its finite \
subgroups and each of those is a finite direct sum of cyclic groups. The two strict-henselization \
inputs are hypotheses — `hdep`, that the canonical map depends only on the inverse image on \
Spec O^sh_{X,x}, and `hconst`, that a locally constant sheaf is constant there with value its \
stalk — as are `hcolim`, which is Tag 03Q5 for the affine variety of vanishing cycles, and \
`hadd`, additivity of RGamma"]
theorem isLocallyAcyclicRelative_of_isLocallyConstant
    (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
    (f : X ⟶ S)
    (hadd : ∀ (x : GeometricPoint X)
        (t : GeometricPoint (strictHenselization B S hS (x.map f))),
      (smallEtaleDerivedGlobalSections (vanishingCyclesFibre B hX hS f x t)).Additive)
    (hcolim : ∀ (x : GeometricPoint X)
        (t : GeometricPoint (strictHenselization B S hS (x.map f))),
      ∀ {I : Type (u + 1)} [SmallCategory I] [IsFiltered I] (N : I ⥤ Ab.{u + 1})
        (c : Cocone N), IsColimit c →
        (∀ i, IsIso ((vanishingCyclesFibreMap B hX hS f x t).app
            (smallEtaleConstantComplexAb X (N.obj i)))) →
          IsIso ((vanishingCyclesFibreMap B hX hS f x t).app
            (smallEtaleConstantComplexAb X c.pt)))
    (hdep : ∀ (x : GeometricPoint X)
        (t : GeometricPoint (strictHenselization B S hS (x.map f)))
        (K K' : smallEtaleDerivedCategory X),
      ((smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K ≅
          (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K') →
      (IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K) ↔
        IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K')))
    (hconst : ∀ (G : Sheaf X.smallEtaleTopology Ab.{u + 1}),
        Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology G →
        ∀ x : GeometricPoint X,
      (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj G) ≅
        (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj
          (smallEtaleConstantComplexAb X ((smallEtaleStalkAb x.hom).obj G)))
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (hf : IsLocallyAcyclic B hX hS f) :
    IsLocallyAcyclicRelative B hX hS f
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F) := by
  intro x t
  rw [hdep x t _ _ (hconst F hFlc x)]
  have := hadd x t
  exact isIso_app_of_torsion
    (Functor.whiskerLeft (smallEtaleConstantComplexFunctor X)
      (vanishingCyclesFibreMap B hX hS f x t))
    (fun N c hc hi => hcolim x t N c hc hi)
    (fun n hn hcop => hf x n hn hcop t)
    ((smallEtaleStalkAb x.hom).obj F) (hFtors x)

end AlgebraicGeometry

end
