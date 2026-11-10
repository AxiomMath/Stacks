module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The subsite of objects flat over a terminal object

Let `(C, K)` be a site with fibre products, `R` a presheaf of commutative rings on `C` and `T₀`
a terminal object. An object `Y` is *flat over `T₀`* when the ring map `R(T₀) ⟶ R(Y)` is flat.
On the full subcategory of such objects the families of morphisms with flat ring maps which
cover in `K` form a coverage, provided flat ring maps are stable under base change along fibre
products of `C` (on affine schemes: the ring of a fibre product is a pushout). For the topology
it generates the inclusion into `C` is continuous, and it is cocontinuous as soon as every
covering sieve of an object flat over `T₀` contains such a family.

This is the site on which a sheaf on a big site of affine schemes over an affine `T₀` is compared
with the base change presheaf `Y ↦ R(Y) ⊗_{R(T₀)} M`: base change along flat ring maps is exact.

## Main definitions

* `Stacks.FlatObjectsSubsite.IsFlatOver`: objects flat over `T₀`.
* `Stacks.FlatObjectsSubsite.coverage`: the families of flat morphisms covering in `K`.
* `Stacks.FlatObjectsSubsite.topology`: the Grothendieck topology they generate.

## Main results

* `Stacks.FlatObjectsSubsite.ι_isContinuous`: the inclusion is continuous.
* `Stacks.FlatObjectsSubsite.ι_isCocontinuous`: the inclusion is cocontinuous.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.FlatObjectsSubsite

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{w}) {T₀ : C} (hT₀ : IsTerminal T₀)

/-- An object is *flat over `T₀`* when the ring map `R(T₀) ⟶ R(Y)` is flat. -/
def IsFlatOver : ObjectProperty C := fun Y ↦ (R.map (hT₀.from Y).op).hom.Flat

/-- The full subcategory of objects flat over `T₀`. -/
abbrev FlatObjects := (IsFlatOver R hT₀).FullSubcategory

variable {R hT₀}

/-- If `Y` is flat over `T₀` and `f : Y' ⟶ Y` has a flat ring map `R(Y) ⟶ R(Y')`, then `Y'`
is flat over `T₀`. -/
lemma isFlatOver_of_flat {Y Y' : C} (f : Y' ⟶ Y) (hf : (R.map f.op).hom.Flat)
    (hY : IsFlatOver R hT₀ Y) : IsFlatOver R hT₀ Y' := by
  change (R.map (hT₀.from Y').op).hom.Flat
  rw [show hT₀.from Y' = f ≫ hT₀.from Y from hT₀.hom_ext _ _, op_comp, R.map_comp,
    CommRingCat.hom_comp]
  exact RingHom.Flat.comp hY hf

variable (R hT₀)

/-- The terminal object `T₀` is flat over itself. -/
lemma isFlatOver_self : IsFlatOver R hT₀ T₀ := by
  change (R.map (hT₀.from T₀).op).hom.Flat
  rw [show hT₀.from T₀ = 𝟙 T₀ from hT₀.hom_ext _ _, op_id, R.map_id]
  exact RingHom.Flat.id _

/-- `T₀` as an object flat over itself. -/
abbrev terminalObj : FlatObjects R hT₀ := ⟨T₀, isFlatOver_self R hT₀⟩

/-- `T₀` is terminal among the objects flat over it. -/
noncomputable def isTerminal : IsTerminal (terminalObj R hT₀) :=
  IsTerminal.ofUniqueHom (fun Y ↦ ObjectProperty.homMk (hT₀.from Y.obj))
    (fun _ _ ↦ ObjectProperty.hom_ext _ (hT₀.hom_ext _ _))

variable (K : GrothendieckTopology C) [HasPullbacks C]
  (hbc : ∀ {P Y₁ Y₂ Y₀ : C} {fst : P ⟶ Y₁} {snd : P ⟶ Y₂} {f : Y₁ ⟶ Y₀} {g : Y₂ ⟶ Y₀},
    IsPullback fst snd f g → (R.map g.op).hom.Flat → (R.map fst.op).hom.Flat)

include hbc in
/-- If `φ : Z ⟶ Y` has a flat ring map and `Y'` is flat over `T₀`, then the fibre product of
`φ` and `f : Y' ⟶ Y` is flat over `T₀`. -/
lemma isFlatOver_pullback {Y Y' Z : C} (φ : Z ⟶ Y) (f : Y' ⟶ Y) (hφ : (R.map φ.op).hom.Flat)
    (hY' : IsFlatOver R hT₀ Y') : IsFlatOver R hT₀ (pullback φ f) :=
  isFlatOver_of_flat (pullback.snd φ f) (hbc (IsPullback.of_hasPullback φ f).flip hφ) hY'

include hbc in
/-- **The families of morphisms with flat ring maps which cover in `K`**, on the objects flat
over `T₀`. -/
def coverage : Coverage (FlatObjects R hT₀) where
  coverings Y := {P | ∃ (I : Type v) (Z : I → FlatObjects R hT₀) (φ : ∀ i, Z i ⟶ Y),
    P = Presieve.ofArrows Z φ ∧ (∀ i, (R.map (φ i).hom.op).hom.Flat) ∧
      Sieve.ofArrows (fun i ↦ (Z i).obj) (fun i ↦ (φ i).hom) ∈ K Y.obj}
  pullback Y Y' f P := by
    rintro ⟨I, Z, φ, rfl, hflat, hcov⟩
    let Z' : I → FlatObjects R hT₀ := fun i ↦
      ⟨pullback (φ i).hom f.hom, isFlatOver_pullback R hT₀ hbc _ _ (hflat i) Y'.property⟩
    let φ' : ∀ i, Z' i ⟶ Y' := fun i ↦ ObjectProperty.homMk (pullback.snd (φ i).hom f.hom)
    refine ⟨Presieve.ofArrows Z' φ', ⟨I, Z', φ', rfl,
      fun i ↦ hbc (IsPullback.of_hasPullback (φ i).hom f.hom).flip (hflat i), ?_⟩, ?_⟩
    · refine K.superset_covering ?_ (K.pullback_stable f.hom hcov)
      rintro W h ⟨V, g₁, g₂, ⟨i⟩, hg⟩
      have hmem := (Sieve.ofArrows (fun i ↦ (Z' i).obj) (fun i ↦ (φ' i).hom)).downward_closed
        (Sieve.ofArrows_mk (fun i ↦ (Z' i).obj) (fun i ↦ (φ' i).hom) i)
        (pullback.lift g₁ h hg)
      rwa [show pullback.lift g₁ h hg ≫ (φ' i).hom = h from pullback.lift_snd _ _ _] at hmem
    · rintro W g ⟨i⟩
      exact ⟨Z i, ObjectProperty.homMk (pullback.fst (φ i).hom f.hom), φ i,
        Presieve.ofArrows.mk i, ObjectProperty.hom_ext _ pullback.condition⟩

omit [HasPullbacks C] in
variable {R hT₀} in
/-- An object isomorphic to an object flat over `T₀` is flat over `T₀`. -/
lemma isFlatOver_of_iso {Y Y' : C} (e : Y ≅ Y') (hY : IsFlatOver R hT₀ Y) :
    IsFlatOver R hT₀ Y' :=
  isFlatOver_of_flat e.inv (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (R.map e.inv.op))) hY

omit [HasPullbacks C] in
include hbc in
/-- **The finite products over `T₀` of objects flat over `T₀` are flat over `T₀`**: a binary
product over `T₀` is a fibre product, along which flat ring maps are stable. -/
theorem isFlatOver_of_isLimit_fan [HasFiniteWidePullbacks C] :
    ∀ (n : ℕ) (Y : Fin n → Over T₀) (_ : ∀ a, IsFlatOver R hT₀ (Y a).left) (c : Fan Y)
      (_ : IsLimit c), IsFlatOver R hT₀ c.pt.left
  | 0, Y, _, c, hc => by
    have hc' : IsTerminal c.pt :=
      IsTerminal.ofUniqueHom (fun Z ↦ hc.lift (Fan.mk Z (fun i ↦ Fin.elim0 i)))
        (fun _ _ ↦ hc.hom_ext (fun ⟨i⟩ ↦ Fin.elim0 i))
    exact isFlatOver_of_iso ((Over.forget T₀).mapIso
      (Over.mkIdTerminal.uniqueUpToIso hc')) (isFlatOver_self R hT₀)
  | n + 1, Y, hY, c, hc => by
    let c₁ := limit.cone (Discrete.functor fun i : Fin n ↦ Y i.succ)
    have h₁ : IsFlatOver R hT₀ c₁.pt.left :=
      isFlatOver_of_isLimit_fan n (fun i ↦ Y i.succ) (fun i ↦ hY i.succ) c₁ (limit.isLimit _)
    have hY₀ : (R.map (Y 0).hom.op).hom.Flat := by
      rw [hT₀.hom_ext (Y 0).hom (hT₀.from _)]
      exact hY 0
    have h₂ : IsFlatOver R hT₀ (Y 0 ⨯ c₁.pt).left := isFlatOver_of_flat _
      (hbc (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (Y 0) c₁.pt)).flip hY₀) h₁
    exact isFlatOver_of_iso ((Over.forget T₀).mapIso ((extendFanIsLimit Y (limit.isLimit _)
      (prodIsProd (Y 0) c₁.pt)).conePointUniqueUpToIso hc)) h₂

/-- The topology on the objects flat over `T₀` generated by the families of flat morphisms
covering in `K`. -/
abbrev topology : GrothendieckTopology (FlatObjects R hT₀) :=
  (coverage R hT₀ K hbc).toGrothendieck

include hbc in
/-- **A sheaf for `K` satisfies the sheaf condition for a family of flat morphisms between
objects flat over `T₀` which covers in `K`**: the fibre products of pairs of members are again
flat over `T₀`, so compatibility on the subsite is compatibility in `C`. -/
theorem isSheafFor_of_mem_coverage {G : Cᵒᵖ ⥤ Type*} (hG : Presieve.IsSheaf K G)
    {Y : FlatObjects R hT₀} {P : Presieve Y} (hP : P ∈ coverage R hT₀ K hbc Y) :
    Presieve.IsSheafFor ((IsFlatOver R hT₀).ι.op ⋙ G) P := by
  obtain ⟨I, Z, φ, rfl, hflat, hcov⟩ := hP
  have hsf : Presieve.IsSheafFor G (Presieve.ofArrows (fun i ↦ (Z i).obj) (fun i ↦ (φ i).hom)) :=
    (Presieve.isSheafFor_iff_generate _).2 (hG _ hcov)
  rw [Presieve.isSheafFor_arrows_iff] at hsf ⊢
  intro x hx
  refine hsf x (fun i j W gi gj hij ↦ ?_)
  let Pij : FlatObjects R hT₀ := ⟨pullback (φ i).hom (φ j).hom,
    isFlatOver_pullback R hT₀ hbc _ _ (hflat i) (Z j).property⟩
  have h := hx i j Pij (ObjectProperty.homMk (pullback.fst _ _))
    (ObjectProperty.homMk (pullback.snd _ _)) (ObjectProperty.hom_ext _ pullback.condition)
  let l := pullback.lift gi gj hij
  calc G.map gi.op (x i) = G.map (l ≫ pullback.fst (φ i).hom (φ j).hom).op (x i) := by
        rw [pullback.lift_fst]
    _ = G.map l.op (G.map (pullback.fst (φ i).hom (φ j).hom).op (x i)) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = G.map l.op (G.map (pullback.snd (φ i).hom (φ j).hom).op (x j)) := congrArg _ h
    _ = G.map (l ≫ pullback.snd (φ i).hom (φ j).hom).op (x j) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = G.map gj.op (x j) := by rw [pullback.lift_snd]

/-- **The inclusion of the objects flat over `T₀` is continuous.** -/
instance ι_isContinuous : (IsFlatOver R hT₀).ι.IsContinuous (topology R hT₀ K hbc) K where
  op_comp_isSheaf_of_types G := by
    rw [Presieve.isSheaf_coverage]
    intro _ _ hP
    exact isSheafFor_of_mem_coverage R hT₀ K hbc
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.property) hP

/-- **The inclusion of the objects flat over `T₀` is cocontinuous** when every covering sieve of
an object flat over `T₀` contains a covering family of flat morphisms from objects flat over
`T₀`. -/
theorem ι_isCocontinuous
    (hloc : ∀ (Y : FlatObjects R hT₀) (S : Sieve Y.obj), S ∈ K Y.obj →
      ∃ (I : Type v) (Z : I → FlatObjects R hT₀) (φ : ∀ i, Z i ⟶ Y),
        (∀ i, (R.map (φ i).hom.op).hom.Flat) ∧
        Sieve.ofArrows (fun i ↦ (Z i).obj) (fun i ↦ (φ i).hom) ∈ K Y.obj ∧
        ∀ i, S (φ i).hom) :
    (IsFlatOver R hT₀).ι.IsCocontinuous (topology R hT₀ K hbc) K where
  cover_lift {Y} S hS := by
    obtain ⟨I, Z, φ, hflat, hcov, hS'⟩ := hloc Y S hS
    refine Coverage.mem_toGrothendieck_sieves_of_superset _ (R := Presieve.ofArrows Z φ) ?_
      ⟨I, Z, φ, rfl, hflat, hcov⟩
    rintro _ _ ⟨i⟩
    exact hS' i

end Stacks.FlatObjectsSubsite

end
