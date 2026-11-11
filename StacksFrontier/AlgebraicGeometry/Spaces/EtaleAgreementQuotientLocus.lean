module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The largest open subspace on which two morphisms agree

Let `Z` be an algebraic space over a scheme `S` and let `α, β : Z ⟶ Y` be two morphisms into an
fppf sheaf `Y`. The union of all open sets of points of `Z` on whose open subspaces `α` and `β`
agree is open, and `α` and `β` agree on the open subspace it cuts out: a section of that
subspace over an object `T` of the site is covered by the open subschemes of `T` that are the
preimages of the open subspaces in the union, and `Y` is a sheaf. This is the largest open
subspace of `Z` on which `α` and `β` agree.

## Main definitions

* `AlgebraicGeometry.Space.agreementOpenPoints`: the union of the open sets of points of `Z` on
  whose subspaces `α` and `β` agree.
* `AlgebraicGeometry.Space.agreementOpenSubspace`: the subspace of `Z` it cuts out.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_agreementOpenSubspace`: it is an open subspace.
* `AlgebraicGeometry.Space.agreementOpenSubspace_ι_comp_eq`: `α` and `β` agree on it.
* `AlgebraicGeometry.Space.le_agreementOpenSubspace`: every open subspace on which `α` and `β` agree
  is contained in it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The union of all open sets `W` of points of `Z` such that `α` and `β` agree on the subspace
of `Z` cut out by `W`. -/
def agreementOpenPoints (α β : Z ⟶ Y) : Set (points B S hS Z) :=
  ⋃₀ {W | IsOpen W ∧
    (openSubspaceOfPoints B S hS Z W).ι ≫ α = (openSubspaceOfPoints B S hS Z W).ι ≫ β}

/-- The set of points on which two morphisms agree locally is open. -/
theorem isOpen_agreementOpenPoints (α β : Z ⟶ Y) : IsOpen (agreementOpenPoints α β) :=
  isOpen_sUnion fun _ h => h.1

/-- The largest open subspace of `Z` on which `α` and `β` agree: the subspace cut out by
`AlgebraicGeometry.Space.agreementOpenPoints`. -/
def agreementOpenSubspace (α β : Z ⟶ Y) : Subfunctor Z :=
  openSubspaceOfPoints B S hS Z (agreementOpenPoints α β)

/-- The agreement locus of two morphisms out of an algebraic space is an open subspace. -/
theorem isOpenSubspace_agreementOpenSubspace (hZ : IsAlgebraicSpace B S hS Z) (α β : Z ⟶ Y) :
    IsOpenSubspace B S hS (agreementOpenSubspace α β) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hZ _ (isOpen_agreementOpenPoints α β)

/-- The points of the agreement locus are `AlgebraicGeometry.Space.agreementOpenPoints`. -/
theorem range_pointsMap_ι_agreementOpenSubspace (α β : Z ⟶ Y) :
    Set.range (pointsMap B S hS (agreementOpenSubspace α β).toFunctor
        (agreementOpenSubspace α β).ι) =
      agreementOpenPoints α β :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- Two elements of a sheaf over an object of the site which agree after restriction along
the members of a jointly surjective family of open immersions are equal. -/
private theorem eq_of_openCover_of_isSheaf
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {T : BigFppfOver B S hS} {K : Type (u + 1)} {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    {a b : Y.obj (op T)} (h : ∀ k, Y.map (p k).op a = Y.map (p k).op b) : a = b := by
  have hY' : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hY
  refine (hY' _ (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hoi
    hcov)).isSeparatedFor.ext ?_
  rintro T' e ⟨Z', l, e', ⟨k⟩, hcomp⟩
  rw [← hcomp, op_comp, Functor.map_comp, types_comp_apply, types_comp_apply, h k]

/-- Two morphisms into an fppf sheaf agree on their agreement locus. -/
theorem agreementOpenSubspace_ι_comp_eq (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (α β : Z ⟶ Y) : (agreementOpenSubspace α β).ι ≫ α = (agreementOpenSubspace α β).ι ≫ β := by
  ext T ⟨x, hx⟩
  change α.app T x = β.app T x
  set q : yoneda.obj T.unop ⟶ Z := yonedaEquiv.symm x with hqdef
  let Kt := {W : Set (points B S hS Z) // IsOpen W ∧
    (openSubspaceOfPoints B S hS Z W).ι ≫ α = (openSubspaceOfPoints B S hS Z W).ι ≫ β}
  have hloc : ∀ k : Kt, ∃ (b : BigFppfOver B S hS) (i : b ⟶ T.unop),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      (∀ p : FieldValuedPoint B S hS (yoneda.obj T.unop),
        pointsMap B S hS (yoneda.obj T.unop) q (p.class B S hS (yoneda.obj T.unop)) ∈ k.1 →
          schemePoint B S hS T.unop p ∈ Set.range ((BigFppfOver.toScheme B S hS).map i)) ∧
      Z.map i.op x ∈ (openSubspaceOfPoints B S hS Z k.1).obj (op b) := by
    intro k
    obtain ⟨V, hV, hpoints⟩ := (isOpen_pointTopology_iff B S hS k.1).1 k.2.1 T.unop q
    obtain ⟨b, i, hi, hir, hiuniv⟩ := exists_restrict_bigFppfOver T.unop ⟨V, hV⟩
    have hkey := range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS k.1 q i V hir
      hiuniv hpoints
    refine ⟨b, i, hi, fun p hp => hir ▸ (hpoints p).1 hp, ?_⟩
    have hmem : (𝟙 b : b ⟶ b) ≫ i ∈ (Subfunctor.range (yoneda.map i)).obj (op b) :=
      ⟨𝟙 b, rfl⟩
    rw [hkey] at hmem
    have : q.app (op b) ((𝟙 b : b ⟶ b) ≫ i) = Z.map i.op x := by
      rw [Category.id_comp]
      rfl
    rw [← this]
    exact hmem
  choose b i hi hcover hmem using hloc
  refine eq_of_openCover_of_isSheaf hY i hi ?_ fun k => ?_
  · intro t
    obtain ⟨p, rfl⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS T.unop t
    have hp : pointsMap B S hS (yoneda.obj T.unop) q (p.class B S hS (yoneda.obj T.unop)) ∈
        agreementOpenPoints α β := hx ⟨_, rfl⟩
    obtain ⟨W, ⟨hWo, hWe⟩, hpW⟩ := hp
    exact ⟨⟨W, hWo, hWe⟩, hcover ⟨W, hWo, hWe⟩ p hpW⟩
  · rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg (fun m => m.app (op (b k)) ⟨_, hmem k⟩) k.2.2

/-- Every open subspace of an algebraic space on which two morphisms agree is contained in
their agreement locus. -/
theorem le_agreementOpenSubspace (hZ : IsAlgebraicSpace B S hS Z) {α β : Z ⟶ Y} {V : Subfunctor Z}
    (hV : IsOpenSubspace B S hS V) (h : V.ι ≫ α = V.ι ≫ β) : V ≤ agreementOpenSubspace α β := by
  refine le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_agreementOpenSubspace hZ α β) ?_
  rw [range_pointsMap_ι_agreementOpenSubspace]
  have hopen : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2
  have hVeq := eq_openSubspaceOfPoints_range_pointsMap_ι B S hS hZ hV
  refine Set.subset_sUnion_of_mem ⟨hopen, ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = Set.range (pointsMap B S hS V.toFunctor V.ι) := ⟨_, rfl⟩
  rw [← hW] at hVeq ⊢
  subst hVeq
  exact h

end AlgebraicGeometry.Space

end
