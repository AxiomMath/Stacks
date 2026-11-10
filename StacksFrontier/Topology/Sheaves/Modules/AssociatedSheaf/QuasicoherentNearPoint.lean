module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Limits.EpiMono
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection
public import StacksFrontier.Topology.Sheaves.Sheafify.PreservesMonoEpi
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.FreeMatrix
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules near a locally quasi-compact point

A quasi-coherent sheaf of modules on a ringed space is, near a point with a fundamental system of
quasi-compact neighbourhoods, the pullback of the sheaf associated to a module over the ring of
sections on a suitable open neighbourhood.

## Main results

* `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso`: **Stacks 01BK**, the open
  neighbourhood, the module and the isomorphism of sheaves of modules.

## Implementation notes

The neighbourhood hypothesis is stated at the chosen point: every neighbourhood of it contains a
quasi-compact neighbourhood. Restriction to an open subspace is the canonical pullback along its
inclusion, and the coefficient map for the associated sheaf is the identity on the global sections
of that open subspace.

The argument is the one of the source. A quasi-coherent sheaf has, on some open `V` through the
point, a presentation by free sheaves of modules; the relation map is in general an infinite
matrix, but on an open `U` whose closure sits inside a quasi-compact neighbourhood contained in
`V` each of its columns is finite, because a section of a free sheaf of modules is locally a
finite combination of the basis sections and a quasi-compact set is covered by finitely many of
the opens witnessing that. Restricting the presentation to `U` therefore gives a matrix over the
ring of sections, and
`Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_unit_matrix` identifies its cokernel with an
associated sheaf.

Local finiteness of the basis expansion is
`Stacks.SheafOfModules.LocallySurjective.freeUnderlyingPresheafLocallySurjective`: the free
sheaf of modules on `I` is the sheafification of the coproduct of copies of the structure
presheaf, so the comparison from that presheaf coproduct is locally surjective. It is proved
by exhibiting the comparison as the sheafification unit up to a locally injective isomorphism,
rather than by an induction on sections.

The proof is split over several private declarations — `exists_truncation_of_compact`,
`exists_matrix_of_compact` — purely so that each elaboration fits the default heartbeat budget;
the restriction functor is left abstract in `exists_matrix_of_compact`, with its agreement with
`restrictOver` as a hypothesis, so that the agreement is checked on abstract morphisms instead of
on the presentation of a quasi-coherent sheaf.

## References

* [Stacks Project, Tag 01BK](https://stacks.math.columbia.edu/tag/01BK)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Filter Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped Topology
open RingedSpaceModuleAdjunction

namespace Stacks.AssociatedSheaf

universe u

open scoped DirectSum
attribute [local instance] Classical.propDecidable

private lemma exists_sum_of_isColimit {I : Type u} {A : I → AddCommGrpCat.{u}}
    {c : Cofan A} (hc : IsColimit c) (s : c.pt) :
    ∃ (t : Finset I) (a : ∀ i, A i), s = ∑ i ∈ t, c.inj i (a i) := by
  classical
  let B := AddCommGrpCat.of (⨁ i, A i)
  let b : Cofan A := Cofan.mk B (fun i ↦ AddCommGrpCat.ofHom (DirectSum.of (fun i ↦ ↥(A i)) i))
  let f : B ⟶ c.pt := AddCommGrpCat.ofHom (DirectSum.toAddMonoid (fun i ↦ (c.inj i).hom))
  have hf : hc.desc b ≫ f = 𝟙 c.pt := by
    apply hc.hom_ext
    rintro ⟨i⟩
    rw [← Category.assoc, hc.fac]
    ext x
    exact DirectSum.toAddMonoid_of (fun i ↦ (c.inj i).hom) i x
  let a : ⨁ i, A i := hc.desc b s
  refine ⟨a.support, a, ?_⟩
  have ha : f a = s := congrArg (fun g : c.pt ⟶ c.pt ↦ g s) hf
  rw [← ha]
  conv_lhs => rw [← DirectSum.sum_support_of a, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ DirectSum.toAddMonoid_of (fun i ↦ (c.inj i).hom) i (a i)

private lemma presheaf_coproduct_image_eq_sum {C : Type u} [Category.{u} C]
    {I : Type u} {A : I → C ⥤ AddCommGrpCat.{u}} {B : C ⥤ AddCommGrpCat.{u}}
    (f : ∀ i, A i ⟶ B) (W : C) (s : (∐ A).obj W) :
    ∃ (t : Finset I) (a : ∀ i, (A i).obj W),
      (Sigma.desc f).app W s = ∑ i ∈ t, (f i).app W (a i) := by
  let c : Cofan (fun i ↦ (A i).obj W) := Cofan.mk ((∐ A).obj W)
    (fun i ↦ (Sigma.ι A i).app W)
  have hc : IsColimit c := (Cofan.isColimitMapCoconeEquiv
    ((evaluation C AddCommGrpCat).obj W) A _)
    (isColimitOfPreserves ((evaluation C AddCommGrpCat).obj W) (coproductIsCoproduct A))
  obtain ⟨t, a, ha⟩ := exists_sum_of_isColimit hc s
  refine ⟨t, a, ?_⟩
  rw [ha, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change ((Sigma.ι A i).app W ≫ (Sigma.desc f).app W) (a i) = _
  rw [← NatTrans.comp_app, Sigma.ι_comp_desc]

section Projections
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private noncomputable def freeTruncation {I : Type u} (t : Finset I) :
    SheafOfModules.free (R := R) I ⟶ SheafOfModules.free I :=
  ∑ i ∈ t, SheafOfModules.freeProjection (R := R) i ≫ SheafOfModules.ιFree i

private lemma free_inclusion_truncation {I : Type u} (t : Finset I) (i : I) (hi : i ∈ t) :
    SheafOfModules.ιFree i ≫ freeTruncation R t = SheafOfModules.ιFree i := by
  classical
  simp [freeTruncation, Preadditive.comp_sum, ← Category.assoc,
    SheafOfModules.ιFree_comp_freeProjection, ite_comp, hi]
end Projections

private noncomputable def restrictOver {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {V U : Opens X} (hUV : U ≤ V) :
    SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} (R.over U) :=
  SheafOfModules.pushforward (F := Over.map (homOfLE hUV)) (𝟙 _)

private instance restrictOver_isLeftAdjoint {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {V U : Opens X} (hUV : U ≤ V) :
    (restrictOver R hUV).IsLeftAdjoint := by
  have h1 : (Over.map (homOfLE hUV)).IsLeftAdjoint :=
    (Over.mapPullbackAdj (homOfLE hUV)).isLeftAdjoint
  dsimp only [restrictOver]
  exact @SheafOfModules.isLeftAdjoint_pushforward_of_isIso
    _ _ _ _ _ _ _ _ _ _ (𝟙 _) _ (IsIso.id _) _

private instance restrictOver_preservesColimitsOfSize {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {V U : Opens X} (hUV : U ≤ V) :
    PreservesColimitsOfSize.{u, u} (restrictOver R hUV) := inferInstance

private lemma exists_open_subset_compact_subset (X : TopCat.{u}) (x : X)
    (hx : ∀ V : Set X, V ∈ 𝓝 x →
      ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x ∧ K ⊆ V)
    (V : Opens X) (hxV : x ∈ V) :
    ∃ U : Opens X, x ∈ U ∧ ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x ∧
      (U : Set X) ⊆ K ∧ K ⊆ V := by
  obtain ⟨K, hK, hKn, hKV⟩ := hx V (V.isOpen.mem_nhds hxV)
  obtain ⟨W, hWK, hW, hxW⟩ := mem_nhds_iff.mp hKn
  exact ⟨⟨W, hW⟩, hxW, K, hK, hKn, hWK, hKV⟩

section LocalSupport

variable {X : RingedSpace.{u, u}}
  {R : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}}
  [∀ V : Opens X.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem freeUnderlyingPresheaf_localPreimage
    {X : RingedSpace.{u, u}}
    {R : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}}
    [∀ V : Opens X.carrier,
      HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
    [∀ V : Opens X.carrier,
      ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (V : Opens X) (I : Type u)
    (s : (SheafOfModules.free (R := R.over V) I).val.presheaf.obj
      (op (Over.mk (𝟙 V)))) {x : X} (hxV : x ∈ V) :
    ∃ (W : Opens X) (g : W ⟶ V), x ∈ W ∧
      ∃ a : (∐ fun _ : I => (SheafOfModules.unit (R.over V)).val.presheaf).obj
        (op (Over.mk g)),
        (Limits.Sigma.desc (fun j : I =>
          (PresheafOfModules.toPresheaf (R.over V).obj).map
            ((SheafOfModules.forget (R.over V)).map
              (SheafOfModules.ιFree (R := R.over V) j)))).app (op (Over.mk g)) a =
          (SheafOfModules.free (R := R.over V) I).val.presheaf.map
            ((Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)).op) s := by
  let JV := (Opens.grothendieckTopology X.carrier).over V
  let f : (∐ fun _ : I => (SheafOfModules.unit (R.over V)).val.presheaf) ⟶
      (SheafOfModules.free (R := R.over V) I).val.presheaf :=
    Limits.Sigma.desc (fun j : I =>
      (PresheafOfModules.toPresheaf (R.over V).obj).map
        ((SheafOfModules.forget (R.over V)).map
          (SheafOfModules.ιFree (R := R.over V) j)))
  have hs : CategoryTheory.Presheaf.imageSieve f s ∈ JV (Over.mk (𝟙 V)) :=
    (Stacks.SheafOfModules.LocallySurjective.freeUnderlyingPresheafLocallySurjective
      (R := R) V I).imageSieve_mem s
  have hsV : Sieve.overEquiv (Over.mk (𝟙 V)) (CategoryTheory.Presheaf.imageSieve f s) ∈
      Opens.grothendieckTopology X.carrier V :=
    (GrothendieckTopology.mem_over_iff
      (J := Opens.grothendieckTopology X.carrier) (Y := Over.mk (𝟙 V))
      (S := CategoryTheory.Presheaf.imageSieve f s)).mp hs
  obtain ⟨W, g, hg, hxW⟩ := hsV x hxV
  have hg' : CategoryTheory.Presheaf.imageSieve f s
      (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)) :=
    (Sieve.overEquiv_iff _ _).mp hg
  obtain ⟨a, ha⟩ := hg'
  exact ⟨W, g, hxW, a, ha⟩

private theorem compact_subset_finite_localPreimages
    {X : RingedSpace.{u, u}}
    {R : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}}
    [∀ V : Opens X.carrier,
      HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
    [∀ V : Opens X.carrier,
      ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (V : Opens X) (K : Set X) (hK : IsCompact K) (hKV : K ⊆ V)
    (I : Type u)
    (s : (SheafOfModules.free (R := R.over V) I).val.presheaf.obj
      (op (Over.mk (𝟙 V)))) :
    ∃ (W : K → Opens X) (g : ∀ k, W k ⟶ V)
      (a : ∀ k, (∐ fun _ : I => (SheafOfModules.unit (R.over V)).val.presheaf).obj
        (op (Over.mk (g k)))),
      (∀ k, (k : X) ∈ W k) ∧
      (∀ k, (Limits.Sigma.desc (fun j : I =>
        (PresheafOfModules.toPresheaf (R.over V).obj).map
          ((SheafOfModules.forget (R.over V)).map
            (SheafOfModules.ιFree (R := R.over V) j)))).app (op (Over.mk (g k))) (a k) =
        (SheafOfModules.free (R := R.over V) I).val.presheaf.map
          ((Over.homMk (g k) : Over.mk (g k) ⟶ Over.mk (𝟙 V)).op) s) ∧
      ∃ t : Finset K, ∀ x ∈ K, ∃ k ∈ t, (x : X) ∈ W k := by
  choose W g hW a ha using fun k : K ↦
    freeUnderlyingPresheaf_localPreimage (R := R) V I s (hKV k.2)
  have hcover : K ⊆ ⋃ k : K, (W k : Set X) := fun x hx ↦
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hW ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k => (W k : Set X))
    (fun k => (W k).isOpen) hcover
  refine ⟨W, g, a, hW, ha, t, fun x hx ↦ ?_⟩
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact ⟨k, hk, hxk⟩

private theorem compact_free_section_truncation
    (V U : Opens X) (K : Set X) (hK : IsCompact K)
    (hUK : (U : Set X) ⊆ K) (hKV : K ⊆ V) (I : Type u)
    (s : (SheafOfModules.free (R := R.over V) I).val.presheaf.obj
      (op (Over.mk (𝟙 V)))) :
    ∃ t : Finset I,
      let g : U ⟶ V := homOfLE (hUK.trans hKV)
      let r := (SheafOfModules.free (R := R.over V) I).val.presheaf.map
        ((Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)).op) s
      (freeTruncation (R.over V) t).val.app (op (Over.mk g)) r = r := by
  classical
  obtain ⟨W, g, a, hW, ha, t, ht⟩ :=
    compact_subset_finite_localPreimages (R := R) V K hK hKV I s
  let f : ∀ j : I, (SheafOfModules.unit (R.over V)).val.presheaf ⟶
      (SheafOfModules.free (R := R.over V) I).val.presheaf := fun j ↦
    (PresheafOfModules.toPresheaf (R.over V).obj).map
      ((SheafOfModules.forget (R.over V)).map (SheafOfModules.ιFree j))
  choose T c hc using fun k ↦ presheaf_coproduct_image_eq_sum f (op (Over.mk (g k))) (a k)
  let T' := t.biUnion T
  let F := SheafOfModules.free (R := R.over V) I
  let p := (PresheafOfModules.toPresheaf (R.over V).obj).map
    (freeTruncation (R.over V) T').val
  have hfix (k : K) (hk : k ∈ t) :
      p.app (op (Over.mk (g k))) (F.val.presheaf.map
        ((Over.homMk (g k) : Over.mk (g k) ⟶ Over.mk (𝟙 V)).op) s) =
        F.val.presheaf.map ((Over.homMk (g k) : Over.mk (g k) ⟶ Over.mk (𝟙 V)).op) s := by
    have h1 : (Limits.Sigma.desc f).app (op (Over.mk (g k))) (a k) =
        F.val.presheaf.map ((Over.homMk (g k) : Over.mk (g k) ⟶ Over.mk (𝟙 V)).op) s := ha k
    rw [← h1, hc k]
    refine Eq.trans (map_sum (p.app (op (Over.mk (g k)))).hom _ _) ?_
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    exact congrArg (fun q ↦ q.val.app (op (Over.mk (g k))) (c k i))
      (free_inclusion_truncation (R.over V) T' i (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩))
  let gU : U ⟶ V := homOfLE (hUK.trans hKV)
  let r := F.val.presheaf.map ((Over.homMk gU : Over.mk gU ⟶ Over.mk (𝟙 V)).op) s
  refine ⟨T', ?_⟩
  change p.app (op (Over.mk gU)) r = r
  let S := Presheaf.equalizerSieve (p.app (op (Over.mk gU)) r) r
  apply F.isSheaf.isSeparated _ S ?_ _ _ (fun Y f hf ↦ hf)
  refine (GrothendieckTopology.mem_over_iff _ _).mpr fun y hy ↦ ?_
  obtain ⟨k, hk, hyk⟩ := ht y (hUK hy)
  let Z : Opens X := U ⊓ W k
  let b : Z ⟶ U := homOfLE inf_le_left
  let a' : Z ⟶ W k := homOfLE inf_le_right
  let b' : Over.mk (b ≫ gU) ⟶ Over.mk gU := Over.homMk b
  let a'' : Over.mk (b ≫ gU) ⟶ Over.mk (g k) := Over.homMk a'
  refine ⟨Z, b, (Sieve.overEquiv_iff _ _).mpr ?_, ⟨hy, hyk⟩⟩
  change F.val.presheaf.map b'.op (p.app (op (Over.mk gU)) r) =
    F.val.presheaf.map b'.op r
  have hres : F.val.presheaf.map b'.op r = F.val.presheaf.map a''.op
      (F.val.presheaf.map ((Over.homMk (g k) : Over.mk (g k) ⟶ Over.mk (𝟙 V)).op) s) := by
    dsimp only [r]
    simp only [← CategoryTheory.comp_apply, ← F.val.presheaf.map_comp, ← op_comp]
    congr 2
  refine Eq.trans (NatTrans.naturality_apply p b'.op r).symm ?_
  refine Eq.trans (congrArg (p.app (op (Over.mk (b ≫ gU)))) hres) ?_
  refine Eq.trans (NatTrans.naturality_apply p a''.op _) ?_
  exact (congrArg (fun z ↦ F.val.presheaf.map a''.op z) (hfix k hk)).trans hres.symm

private theorem compact_free_hom_truncation
    (V U : Opens X) (K : Set X) (hK : IsCompact K)
    (hUK : (U : Set X) ⊆ K) (hKV : K ⊆ V) (I : Type u)
    (f : SheafOfModules.unit (R.over V) ⟶ SheafOfModules.free I) :
    ∃ t : Finset I,
      (restrictOver R (hUK.trans hKV)).map (f ≫ freeTruncation (R.over V) t) =
        (restrictOver R (hUK.trans hKV)).map f := by
  let g : U ⟶ V := homOfLE (hUK.trans hKV)
  obtain ⟨t, ht⟩ := compact_free_section_truncation (R := R) V U K hK hUK hKV I
    (f.val.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V)))
  refine ⟨t, ?_⟩
  apply unit_hom_ext_of_app_terminal (Over.mk (𝟙 U)) Over.mkIdTerminal
  change (freeTruncation (R.over V) t).val.app (op (Over.mk g))
    (f.val.app (op (Over.mk g)) (1 : R.obj.obj (op U))) =
      f.val.app (op (Over.mk g)) (1 : R.obj.obj (op U))
  have hn := PresheafOfModules.naturality_apply f.val
    ((Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)).op) (1 : R.obj.obj (op V))
  have h1 : (SheafOfModules.unit (R.over V)).val.map
      ((Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)).op)
      (1 : R.obj.obj (op V)) = (1 : R.obj.obj (op U)) := (R.obj.map g.op).hom.map_one
  rw [h1] at hn
  change f.val.app (op (Over.mk g)) (1 : R.obj.obj (op U)) =
    (SheafOfModules.free (R := R.over V) I).val.presheaf.map
      ((Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)).op)
      (f.val.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V))) at hn
  dsimp only at ht
  rwa [← hn] at ht

end LocalSupport

/-- `compact_free_hom_truncation` for the structure sheaf of a ringed space, with its
sheafification instances discharged once. -/
private lemma exists_truncation_of_compact {X : RingedSpace.{u, u}} (V U : Opens X.carrier)
    (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) (hKV : K ⊆ V) (hUV : U ≤ V)
    {I : Type u}
    (φ : SheafOfModules.unit ((structureSheafRing X).over V) ⟶ SheafOfModules.free I) :
    ∃ t : Finset I,
      (restrictOver (structureSheafRing X) hUV).map
          (φ ≫ freeTruncation ((structureSheafRing X).over V) t) =
        (restrictOver (structureSheafRing X) hUV).map φ :=
  compact_free_hom_truncation (R := structureSheafRing X) V U K hK hUK hKV I φ

private noncomputable abbrev openSubspace
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) := X.restrict U.isOpenEmbedding

private noncomputable abbrev openInclusion
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) : openSubspace X U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

private instance isContinuous_openSubspace_functor
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology (openSubspace X U).carrier)
      (Opens.grothendieckTopology X.carrier) := by
  change (U.isOpenEmbedding.functor).IsContinuous
    (Opens.grothendieckTopology ((Opens.toTopCat X.carrier).obj U)) _
  exact U.isOpenEmbedding.functor_isContinuous

private noncomputable def openRestrictionFunctor
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (structureSheafRing (openSubspace X U)) :=
  SheafOfModules.pushforward (F := U.isOpenEmbedding.functor) (𝟙 _)

private noncomputable def openRestrictionAdjunction
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    openRestrictionFunctor X U ⊣
      RingedSpaceModuleAdjunction.modulePushforward (openInclusion X U) := by
  letI : (Opens.map U.inclusion').IsContinuous (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology (openSubspace X U).carrier) :=
    RingedSpaceModuleAdjunction.opensMap_isContinuous (openInclusion X U)
  let adj := U.isOpenEmbedding.isOpenMap.adjunction
  refine SheafOfModules.pushforwardPushforwardAdj adj (𝟙 _)
    (RingedSpaceModuleAdjunction.structureSheafHom (openInclusion X U)) ?_ ?_
  · ext V x
    rfl
  · ext V x
    change X.presheaf.map ((U.isOpenEmbedding.functor).map
      (adj.unit.app V.unop)).op
      (X.presheaf.map (adj.counit.app ((U.isOpenEmbedding.functor).obj V.unop)).op x) = x
    have htri := adj.left_triangle_components V.unop
    have hmap : X.presheaf.map
        (adj.counit.app ((U.isOpenEmbedding.functor).obj V.unop)).op ≫
          X.presheaf.map ((U.isOpenEmbedding.functor).map (adj.unit.app V.unop)).op = 𝟙 _ := by
      rw [← X.presheaf.map_comp, ← op_comp, htri]
      simp
    exact congrArg (fun f => f x) hmap

private noncomputable def modulePullbackOpenIso
    (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback (openInclusion X U)).obj F ≅
      (U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U) :=
  ((modulePullbackPushforwardAdjunction (openInclusion X U)).leftAdjointUniq
    (openRestrictionAdjunction X U)).app F

/-- Near a point with a basis of quasi-compact neighbourhoods, the restriction to a small open
of a morphism out of the unit sheaf of modules is a finite matrix in the basis sections.

Keeping this out of `exists_open_associatedSheaf_iso` is what makes each elaboration fit the
default heartbeat budget. The restricting functor `L` is left abstract, with its agreement with
`restrictOver` supplied as `hLmap`, so that the caller's instance of that agreement is checked on
abstract morphisms rather than on the presentation of a quasi-coherent sheaf. -/
private lemma exists_matrix_of_compact {X : RingedSpace.{u, u}} {V U : Opens X.carrier}
    (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) (hKV : K ⊆ V) (hUV : U ≤ V)
    {Y : RingedSpace.{u, u}} {Ig Ir : Type u}
    (L : SheafOfModules.{u} ((structureSheafRing X).over V) ⥤
      SheafOfModules.{u} (structureSheafRing Y))
    [PreservesColimitsOfSize.{u, u} L] [L.Additive]
    (hLmap : ∀ {M N : SheafOfModules.{u} ((structureSheafRing X).over V)} (φ ψ : M ⟶ N),
      (restrictOver (structureSheafRing X) hUV).map φ =
          (restrictOver (structureSheafRing X) hUV).map ψ →
        L.map φ = L.map ψ)
    (η : SheafOfModules.unit (structureSheafRing Y) ≅
      L.obj (SheafOfModules.unit ((structureSheafRing X).over V)))
    (d : SheafOfModules.free (R := (structureSheafRing X).over V) Ir ⟶ SheafOfModules.free Ig)
    (j : Ir) :
    ∃ (t : Finset Ig) (a : Ig → (SheafOfModules.unit (structureSheafRing Y) ⟶
      SheafOfModules.unit (structureSheafRing Y))),
      SheafOfModules.ιFree j ≫ ((SheafOfModules.mapFreeIso L Ir η).hom ≫ L.map d ≫
          (SheafOfModules.mapFreeIso L Ig η).inv) =
        ∑ i ∈ t, a i ≫ SheafOfModules.ιFree i := by
  obtain ⟨t, ht⟩ := exists_truncation_of_compact V U K hK hUK hKV hUV
    (SheafOfModules.ιFree j ≫ d)
  refine ⟨t, fun i ↦ η.hom ≫ L.map ((SheafOfModules.ιFree j ≫ d) ≫
    SheafOfModules.freeProjection (R := (structureSheafRing X).over V) i) ≫ η.inv, ?_⟩
  calc
    SheafOfModules.ιFree j ≫ ((SheafOfModules.mapFreeIso L Ir η).hom ≫ L.map d ≫
          (SheafOfModules.mapFreeIso L Ig η).inv)
        = η.hom ≫ L.map (SheafOfModules.ιFree j ≫ d) ≫
          (SheafOfModules.mapFreeIso L Ig η).inv := by
      simp [Functor.map_comp, Category.assoc]
    _ = η.hom ≫ L.map ((SheafOfModules.ιFree j ≫ d) ≫
        freeTruncation ((structureSheafRing X).over V) t) ≫
        (SheafOfModules.mapFreeIso L Ig η).inv := by rw [hLmap _ _ ht]
    _ = ∑ i ∈ t, (η.hom ≫ L.map ((SheafOfModules.ιFree j ≫ d) ≫
        SheafOfModules.freeProjection (R := (structureSheafRing X).over V) i) ≫ η.inv) ≫
          SheafOfModules.ιFree i := by
      simp [freeTruncation, Preadditive.comp_sum, Preadditive.sum_comp,
        Functor.map_sum, Functor.map_comp, Category.assoc]

/-- **Stacks 01BK.** A quasi-coherent sheaf of modules is locally associated to a
module over the ring of sections near a point with a basis of quasi-compact
neighborhoods. -/
@[stacks 01BK]
public lemma exists_open_associatedSheaf_iso (X : RingedSpace.{u, u}) (x : X)
    (hx : ∀ V : Set X, V ∈ 𝓝 x →
      ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x ∧ K ⊆ V)
    (F : SheafOfModules.{u} (structureSheafRing X)) [F.IsQuasicoherent] :
    ∃ U : Opens X, x ∈ U ∧
      ∃ M : ModuleCat.{u} ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
        Nonempty (((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj F) ≅
          associatedSheaf (X.restrict U.isOpenEmbedding)
            (RingHom.id ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M) := by
  obtain ⟨q⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff X.carrier q.X).mp q.coversTop
  have hxUnion : x ∈ ⋃ i, (q.X i : Set X) := by
    rw [hcov.iSup_set_eq_univ]
    exact Set.mem_univ x
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxUnion
  let V : Opens X := q.X i
  obtain ⟨U, hxU, K, hK, hKn, hUK, hKV⟩ :=
    exists_open_subset_compact_subset X x hx V hxi
  have hUV : U ≤ V := hUK.trans hKV
  have PV : (F.over V).Presentation := q.presentation i
  let Y := X.restrict U.isOpenEmbedding
  let A := restrictOver (structureSheafRing X) hUV
  let E := (U.sheafOfModulesEquivOver (structureSheafRing X)).functor
  let L : SheafOfModules.{u} ((structureSheafRing X).over V) ⥤
      SheafOfModules.{u} (structureSheafRing Y) := A ⋙ E
  have hAc : PreservesColimitsOfSize.{u, u} A :=
    restrictOver_preservesColimitsOfSize (structureSheafRing X) hUV
  have hL : PreservesColimitsOfSize.{u, u} L := by
    change PreservesColimitsOfSize.{u, u} (A ⋙ E)
    infer_instance
  have hAdd : L.Additive := ⟨rfl⟩
  let η : SheafOfModules.unit (structureSheafRing Y) ≅
      L.obj (SheafOfModules.unit ((structureSheafRing X).over V)) := Iso.refl _
  let d : SheafOfModules.free PV.relations.I ⟶ SheafOfModules.free PV.generators.I :=
    (SheafOfModules.freeHomEquiv _).symm PV.relations.s ≫ kernel.ι PV.generators.π
  let eI := SheafOfModules.mapFreeIso L PV.generators.I η
  let eJ := SheafOfModules.mapFreeIso L PV.relations.I η
  let f : SheafOfModules.free (R := structureSheafRing Y) PV.relations.I ⟶
      SheafOfModules.free PV.generators.I := eJ.hom ≫ L.map d ≫ eI.inv
  have hLmap : ∀ {M N : SheafOfModules.{u} ((structureSheafRing X).over V)} (φ ψ : M ⟶ N),
      (restrictOver (structureSheafRing X) hUV).map φ =
          (restrictOver (structureSheafRing X) hUV).map ψ →
        L.map φ = L.map ψ := fun _ _ h ↦ congrArg E.map h
  have hf : ∀ j : PV.relations.I, ∃ (t : Finset PV.generators.I)
      (a : PV.generators.I → (SheafOfModules.unit (structureSheafRing Y) ⟶
        SheafOfModules.unit (structureSheafRing Y))),
      SheafOfModules.ιFree j ≫ f = ∑ i ∈ t, a i ≫ SheafOfModules.ιFree i :=
    exists_matrix_of_compact K hK hUK hKV hUV L hLmap η d
  obtain ⟨M, ⟨eM⟩⟩ := exists_associatedSheaf_iso_of_unit_matrix Y f hf
  let eC : cokernel d ≅ F.over V := colimit.isoColimitCocone ⟨_, PV.isColimit⟩
  have hd : f ≫ eI.hom = eJ.hom ≫ L.map d := by simp [f]
  exact ⟨U, hxU, M, ⟨modulePullbackOpenIso X U F ≪≫ (L.mapIso eC).symm ≪≫
    PreservesCokernel.iso L d ≪≫ (cokernel.mapIso f (L.map d) eJ eI hd).symm ≪≫ eM⟩⟩

end Stacks.AssociatedSheaf
