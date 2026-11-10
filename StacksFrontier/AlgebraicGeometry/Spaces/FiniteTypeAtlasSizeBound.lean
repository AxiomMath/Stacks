module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Deformation.Artin.RimSchlessinger
import all StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion

/-!
# An atlas of bounded size for an algebraic space locally of finite type

Let `F` be an algebraic space over `S` which is locally of finite type over `S` and whose values
on the finite type fields over `S` are bounded by a cardinal `μ` below the cutoff of the site
(axiom [-1] of Section 07XZ). Then `F` has a surjective étale atlas by an object of the site of
size at most `max (2 ^ size S) μ`.

This is the set-theoretic detail of the proof of Stacks 07Y5 that the source omits ("the size
of the algebraic space `Y` representing `𝒴` is suitably bounded. Namely, `Y → S` will be locally
of finite type and `Y` will satisfy axiom [-1]"), in the form the set-theoretic hypothesis of
Stacks 07WH asks for.

The proof follows the source's atlas in Stacks 07Y1: for every finite type field `k` over `S`,
from a set of representatives of size at most `2 ^ size S`, and every element of `F(Spec k)`,
the corresponding finite type point of `F` is the image of a closed point of an affine scheme
étale over `F` (Stacks 06EH); being étale over `F`, that scheme is locally of finite type over
`S`, so its size is at most `size S` (Stacks 04T7). The disjoint union of these charts lies in
the site, maps étale to `F`, and its image is an open set of points containing every finite type
point, hence everything (Stacks 06EK).

## Main results

* `AlgebraicGeometry.Space.exists_atlas_size_le_of_isLocallyOfFiniteType`.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
* [Stacks Project, Tag 07WH](https://stacks.math.columbia.edu/tag/07WH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism from the spectrum of a field is quasi-compact: the preimage of any set is a subset
of a one-point space. -/
theorem quasiCompact_of_spec_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : Spec (.of k) ⟶ X) : QuasiCompact f :=
  ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩

variable {B S hS}

/-- A morphism from a representable presheaf to `F`, composed with the map `F ⟶ *`, is locally of
finite type iff the object is locally of finite type over `S`. -/
private theorem isLocallyOfFiniteType_comp_terminal_iff
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ F) :
    IsLocallyOfFiniteType B S hS (φ ≫ t) ↔ LocallyOfFiniteType (B.inclusion.map U.hom) := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  have : φ ≫ t = yoneda.map (hterm.from U) := yonedaEquiv.injective (hterm.hom_ext _ _)
  have hl : (hterm.from U).left = U.hom := by simpa using Over.w (hterm.from U)
  rw [this, isLocallyOfFiniteType_yoneda_map_iff]
  change LocallyOfFiniteType (B.inclusion.map (hterm.from U).left) ↔ _
  rw [hl]

/-- A section of an algebraic space locally of finite type over `S`, over an object of the site
locally of finite type over `S`, is a morphism locally of finite type. -/
theorem isLocallyOfFiniteType_yonedaEquiv_symm_of_isLocallyOfFiniteType
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (t : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (U : BigFppfOver B S hS) (s : F.obj (op U))
    (hU : LocallyOfFiniteType (B.inclusion.map U.hom)) :
    IsLocallyOfFiniteType B S hS (yonedaEquiv.symm s) :=
  isLocallyOfFiniteType_of_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hF
    (isAlgebraicSpace_yoneda B S hS _) _ t ((isLocallyOfFiniteType_comp_terminal_iff t U _).2 hU)

/-- An object of the site carrying a morphism locally of finite type to an algebraic space
locally of finite type over `S` is locally of finite type over `S`. -/
theorem locallyOfFiniteType_of_isLocallyOfFiniteType_comp
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (t : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (ht : IsLocallyOfFiniteType B S hS t)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ F) (hφ : IsLocallyOfFiniteType B S hS φ) :
    LocallyOfFiniteType (B.inclusion.map U.hom) :=
  (isLocallyOfFiniteType_comp_terminal_iff t U φ).1 <|
    isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hF
      (isAlgebraicSpace_yoneda B S hS _) φ t hφ ht

/-- **An algebraic space locally of finite type over `S` satisfying axiom [-1] has an atlas of
bounded size.** If `F → S` is locally of finite type and `|F(Spec k)| ≤ μ` for every finite
type field `k` over `S`, for a cardinal `μ` below the cutoff of the site, then `F` has a surjective
étale atlas `h_A ⟶ F` by an object `A` of the site with `size A ≤ max (2 ^ size S) μ`. -/
theorem exists_atlas_size_le_of_isLocallyOfFiniteType
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (t : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) (ht : IsLocallyOfFiniteType B S hS t)
    (μ : Cardinal.{u}) (hμ : μ < B.cutoff)
    (hT₀ : ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
      U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        #(F.obj (op U)) ≤ μ) :
    ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      A.left.1.size ≤ max (2 ^ S.size) μ := by
  classical
  let κ := max (2 ^ S.size) μ
  have hκ0 : ℵ₀ ≤ κ := (S.aleph0_le_size.trans (cantor S.size).le).trans (le_max_left _ _)
  have hSκ : S.size ≤ κ := (cantor S.size).le.trans (le_max_left _ _)
  have hκ : κ < B.cutoff := max_lt (B.cutoff_isStrongPrelimit hS) hμ
  let I := Σ d : finiteTypeFieldBaseData S, F.obj (op (fieldBaseOver B S hS d.1))
  have hI : #I ≤ κ := by
    apply sigma_cardinal_le _ hκ0
    · exact ((Cardinal.mk_subtype_le _).trans (fieldBaseData_cardinal_le S)).trans
        (le_max_left _ _)
    · intro d
      let : Field (FreeCommRing S.size.out ⧸ d.1.2.1.1) := fieldBaseField S d.1
      exact (hT₀ (fieldBaseOver B S hS d.1) (FreeCommRing S.size.out ⧸ d.1.2.1.1) rfl
        ⟨d.2.1, d.2.2⟩).trans (le_max_right _ _)
  let p : I → FieldValuedPoint B S hS F := fun i =>
    let : Field (FreeCommRing S.size.out ⧸ i.1.1.2.1.1) := fieldBaseField S i.1.1
    { carrier := FreeCommRing S.size.out ⧸ i.1.1.2.1.1
      contained := fieldBase_spec_mem B S hS i.1.1
      toBase := fieldBaseMap S i.1.1
      value := i.2 }
  have hft (i : I) : IsFiniteTypePoint B S hS F ((p i).class B S hS F) :=
    ⟨p i, rfl, isLocallyOfFiniteType_yonedaEquiv_symm_of_isLocallyOfFiniteType hF t
      (fieldBaseOver B S hS i.1.1) i.2 i.1.2.1⟩
  choose U φ q hUaff hφ _ hmap using fun i =>
    (isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart B S hS F hF _).1 (hft i)
  have hsizeU (i : I) : ((BigFppfOver.toScheme B S hS).obj (U i)).size ≤ κ := by
    have hlft := locallyOfFiniteType_of_isLocallyOfFiniteType_comp hF t ht (U i) (φ i)
      (isLocallyOfFiniteType_of_isEtale' B S hS (φ i) (hφ i))
    have : IsAffine (B.inclusion.obj (U i).left) := hUaff i
    exact (Scheme.size_le_of_locallyOfFiniteType (B.inclusion.map (U i).hom)).trans hSκ
  obtain ⟨Z, c, hoi, hdisj, hcov⟩ :=
    BigFppfOver.exists_coproduct_of_size_le B S hS U hκ0 hκ hI hsizeU
  have hFsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hF.isSheaf
  obtain ⟨τ, hτ⟩ := BigFppfOver.exists_section_of_disjoint_openCover hFsheaf c hoi hdisj hcov
    (fun i => yonedaEquiv (φ i))
  let a : yoneda.obj Z ⟶ F := yonedaEquiv.symm τ
  have hca (i : I) : yoneda.map (c i) ≫ a = φ i := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hτ]
  have hetale : IsEtale B S hS a :=
    isEtale_of_scheme_openCover B S hS hF a U c hoi hcov fun i => hca i ▸ hφ i
  have hsurj : IsSurjective B S hS a := by
    let : TopologicalSpace (points B S hS F) := pointTopology B S hS F
    have hR := isOpen_range_pointsMap_of_isEtale B S hS a (isAlgebraicSpace_yoneda B S hS Z) hF
      hetale
    have hcl := closure_inter_finiteTypePoints B S hS F hF hR.isClosed_compl
    have hempty : (Set.range (pointsMap B S hS (yoneda.obj Z) a))ᶜ ∩
        finiteTypePoints B S hS F = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x ⟨hx, hxft⟩ => hx ?_
      obtain ⟨r, rfl, hr⟩ := hxft
      have : LocallyOfFiniteType r.toBase :=
        locallyOfFiniteType_of_isLocallyOfFiniteType_comp hF t ht _ _ hr
      have : QuasiCompact r.toBase := quasiCompact_of_spec_field r.toBase
      obtain ⟨d, e, he⟩ := exists_finiteTypeFieldBaseMap S r.carrier r.toBase
      let : Field (FreeCommRing S.size.out ⧸ d.1.2.1.1) := fieldBaseField S d.1
      have hw : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ r.toBase = fieldBaseMap S d.1 := by
        have : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ :=
          CommRingCat.hom_ext <| RingHom.ext e.symm_apply_apply
        rw [← he, ← Category.assoc, ← Spec.map_comp, this, Spec.map_id, Category.id_comp]
      let g : fieldBaseOver B S hS d.1 ⟶ r.siteObject B S hS F :=
        Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
          (by apply ObjectProperty.hom_ext; exact hw)
      let i : I := ⟨d, F.map g.op r.value⟩
      have hcls : (p i).class B S hS F = r.class B S hS F :=
        Quot.sound ⟨_, FieldValuedPoint.dominates_refl B S hS F _, ⟨g, rfl⟩⟩
      rw [← hcls, ← hmap i, ← hca i, pointsMap_comp]
      exact ⟨_, rfl⟩
    rw [hempty, closure_empty] at hcl
    exact fun x => by_contra fun hx => Set.notMem_empty x (hcl.symm.subset hx)
  refine ⟨Z, a, (presheafSurjective_iff_isSurjective_yoneda B S hS F hF Z a).2 hsurj,
    (isEtale_iff_presheaf_of_yoneda B S hS a).1 hetale, ?_⟩
  change ((BigFppfOver.toScheme B S hS).obj Z).size ≤ κ
  rcases isEmpty_or_nonempty I with hIe | hIne
  · refine (size_le_aleph0_of_isEmpty _ ⟨fun z => ?_⟩).trans hκ0
    obtain ⟨i, -⟩ := hcov z
    exact hIe.false i
  · let O : I → ((BigFppfOver.toScheme B S hS).obj Z).Opens := fun i =>
      ((BigFppfOver.toScheme B S hS).map (c i)).opensRange
    have hO : ⨆ i, O i = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨i, hi⟩ := hcov z
      exact (TopologicalSpace.Opens.mem_iSup).2 ⟨i, hi⟩
    refine (Scheme.size_le_of_iSup_eq_top O hO).trans (max_le hI (ciSup_le' fun i => ?_))
    have := hoi i
    rw [← Scheme.size_congr ((BigFppfOver.toScheme B S hS).map (c i)).isoOpensRange]
    exact hsizeU i

end AlgebraicGeometry.Space

end
