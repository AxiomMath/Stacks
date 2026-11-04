module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportSheaf
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# The support of an abelian étale sheaf and the supports of its sections

Let `B` be a big étale site containing a scheme `S` and let `F` be an abelian sheaf on the small
étale site of `S` inside `B`. The support of `F` is the set of points of `S` carrying a geometric
point with nonzero stalk, and the support of a section of `F` is the complement of the largest
Zariski open on which the section vanishes. A geometric stalk of `F` is nonzero exactly when some
section over some étale neighbourhood of the geometric point has the chosen lift of that point in
its support; the support of `F` is therefore the union of the images in `S` of the supports of all
local sections of `F`. Consequently a surjection `F ⟶ G` of abelian sheaves confines the support
of `G` to that of `F`, and an injection `F ⟶ G` confines the support of `F` to that of `G`.

## Main results

* `AlgebraicGeometry.etaleGerm_ulift_eq_zero_iff_mem_zeroOpen` — a germ vanishes at a lift of a
  geometric point exactly when that lift lands in the zero locus of the section.
* `AlgebraicGeometry.not_isZero_etaleStalk_iff_exists_mem_supportSection` — the local form of the
  description of the support: a geometric stalk is nonzero exactly when some local section has the
  chosen lift of the geometric point in its support.
* `AlgebraicGeometry.supportSheaf_eq_iUnion_image_supportSection` — **Stacks 04FT, part (4)**.
* `AlgebraicGeometry.supportSheaf_subset_of_isLocallySurjective` — **Stacks 04FT, part (5)**.
* `AlgebraicGeometry.supportSheaf_subset_of_injective` — **Stacks 04FT, part (6)**.
* `AlgebraicGeometry`
  `.isClosed_supportSection_and_supportSheaf_eq_iUnion_image_supportSection_and_subset` —
  **Stacks 04FT** itself, all six of its parts in one statement, assembled from the six theorems
  that each state one part.

## Implementation notes

The support of a sheaf is defined through the stalks of `F` composed with the universe lift of
abelian groups, since the stalk of `F` itself need not exist when the coefficient universe is
smaller than the universe of the schemes. Germs of the lifted presheaf are germs of `F` with
`ULift.up` applied, so the zero locus of a section of `F` still computes them; that is
`AlgebraicGeometry.etaleGerm_ulift_eq_zero_iff_mem_zeroOpen`, and no size hypothesis is needed
anywhere in this file.

Surjectivity of a map of abelian sheaves is local surjectivity, which is what makes such a map an
epimorphism: surjectivity on sections is strictly stronger, so part (5) is stated with
`CategoryTheory.Sheaf.IsLocallySurjective`. Injectivity of a map of abelian sheaves, on the other
hand, is injectivity on every group of sections — equivalently local injectivity, by
`CategoryTheory.Sheaf.isLocallyInjective_iff_injective` — and part (6) is stated that way.

## References

* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
* [Stacks Project, Tag 04FT](https://stacks.math.columbia.edu/tag/04FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

open SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

private theorem ulift_map_eq_zero_iff
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{v}) {X Y : (SmallEtale B S hS)ᵒᵖ} (j : X ⟶ Y)
    (a : P.obj X) :
    (P ⋙ AddCommGrpCat.uliftFunctor.{u, v}).map j (ULift.up a) = 0 ↔ P.map j a = 0 :=
  ⟨fun h => congrArg ULift.down (h : ULift.up (P.map j a) = (0 : ULift.{u} _)),
    fun h => show ULift.up (P.map j a) = 0 from congrArg ULift.up h⟩

/-- A germ of an abelian sheaf at a geometric point vanishes exactly when the chosen lift of that
geometric point lands in the maximal Zariski open zero locus of the section. -/
public theorem etaleGerm_ulift_eq_zero_iff_mem_zeroOpen (t : GeometricPoint S)
    (W : SmallEtale B S hS) (q : (geometricPointFiber B S hS t).obj W)
    (a : F.obj.obj (op W)) :
    etaleGerm B S hS t (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v}) W q (ULift.up a) = 0 ↔
      q.1.base default ∈
        (zeroOpen B S hS F W a : Set ((SmallEtale.toScheme B S hS).obj W)) := by
  constructor
  · intro hgerm
    obtain ⟨W', j, q', hq, hzero⟩ :=
      (etaleGerm_eq_zero_iff B S hS t
        (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v}) W q _).1 hgerm
    refine (map_eq_zero_iff_range_subset_zeroOpen B S hS F W a W' j).1
      ((ulift_map_eq_zero_iff B S hS F.obj j.op a).1 hzero) ⟨q'.1.base default, ?_⟩
    have hcomp : q'.1 ≫ (SmallEtale.toScheme B S hS).map j = q.1 := congrArg Subtype.val hq
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : t.source ⟶ (SmallEtale.toScheme B S hS).obj W => k default) hcomp
  · intro hmem
    refine (etaleGerm_eq_zero_iff B S hS t
        (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v}) W q _).2
      ⟨openObject B S hS W (zeroOpen B S hS F W a),
        openObjectι B S hS W (zeroOpen B S hS F W a),
        openObjectLift B S hS t W q (zeroOpen B S hS F W a) hmem,
        openObjectLift_map B S hS t W q _ hmem, ?_⟩
    exact (ulift_map_eq_zero_iff B S hS F.obj
      (openObjectι B S hS W (zeroOpen B S hS F W a)).op a).2
      ((map_eq_zero_iff_le_zeroOpen B S hS F W a _
        (openObjectι B S hS W (zeroOpen B S hS F W a))).2
        (le_of_eq (openObjectι_opensRange B S hS W (zeroOpen B S hS F W a))))

/-- The stalk of an abelian sheaf at a geometric point is nonzero exactly when some section over
some étale neighbourhood of the point has the chosen lift of the point in its support. -/
public theorem not_isZero_etaleStalk_iff_exists_mem_supportSection (t : GeometricPoint S) :
    ¬ IsZero (etaleStalk B S hS t (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})) ↔
      ∃ (W : SmallEtale B S hS) (q : (geometricPointFiber B S hS t).obj W)
        (a : F.obj.obj (op W)), q.1.base default ∈ supportSection B S hS F W a := by
  constructor
  · intro hnz
    by_contra hno
    simp only [not_exists, supportSection, Set.mem_compl_iff, not_not] at hno
    have hall : ∀ g : ↑(etaleStalk B S hS t
        (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v})), g = 0 := by
      intro g
      obtain ⟨W, q, b, rfl⟩ := exists_etaleGerm_eq B S hS t _ g
      exact (etaleGerm_ulift_eq_zero_iff_mem_zeroOpen B S hS F t W q b.down).2 (hno W q b.down)
    have := subsingleton_of_forall_eq 0 hall
    exact hnz (AddCommGrpCat.isZero_of_subsingleton _)
  · rintro ⟨W, q, a, ha⟩ hz
    have := AddCommGrpCat.subsingleton_of_isZero hz
    exact ha ((etaleGerm_ulift_eq_zero_iff_mem_zeroOpen B S hS F t W q a).1
      (Subsingleton.elim _ _))

/-- **Stacks 04FT, part (4).** The support of an abelian sheaf on the small étale site is the
union, over all objects of the site and all sections of the sheaf over them, of the images in the
base scheme of the supports of those sections. -/
@[stacks 04FT "part (4)"]
public theorem supportSheaf_eq_iUnion_image_supportSection :
    AlgebraicGeometry.supportSheaf B S hS F =
      ⋃ (U : SmallEtale B S hS), ⋃ (a : F.obj.obj (op U)),
        (B.inclusion.map U.obj.hom).base '' supportSection B S hS F U a := by
  ext x
  rw [mem_supportSheaf_iff_exists]
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨t, htx, hnz⟩
    obtain ⟨W, q, a, ha⟩ :=
      (not_isZero_etaleStalk_iff_exists_mem_supportSection B S hS F t).1 hnz
    refine ⟨W, a, q.1.base default, ha, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      (congrArg (fun m : t.source ⟶ S => m default) q.2).trans htx
  · rintro ⟨U, a, y, hy, hyx⟩
    have hp : ((GeometricPoint.ofPoint ((SmallEtale.toScheme B S hS).obj U) y).hom).base
        default = y := GeometricPoint.ofPoint_liesOver ((SmallEtale.toScheme B S hS).obj U) y
    refine ⟨(GeometricPoint.ofPoint ((SmallEtale.toScheme B S hS).obj U) y).map
      (B.inclusion.map U.obj.hom), ?_,
      (not_isZero_etaleStalk_iff_exists_mem_supportSection B S hS F _).2
        ⟨U, ⟨_, rfl⟩, a, by rwa [hp]⟩⟩
    show ((GeometricPoint.ofPoint ((SmallEtale.toScheme B S hS).obj U) y).hom ≫
      B.inclusion.map U.obj.hom) default = x
    rwa [Scheme.Hom.comp_apply, hp]

/-- **Stacks 04FT, part (5).** If a map of abelian sheaves on the small étale site is surjective,
that is locally surjective, then the support of its target is contained in the support of its
source. -/
@[stacks 04FT "part (5)"]
public theorem supportSheaf_subset_of_isLocallySurjective (φ : F ⟶ G)
    [Sheaf.IsLocallySurjective φ] :
    AlgebraicGeometry.supportSheaf B S hS G ⊆ AlgebraicGeometry.supportSheaf B S hS F := by
  rintro x ⟨t, htx, hnz⟩
  refine ⟨t, htx, ?_⟩
  obtain ⟨W, q, b, hb⟩ :=
    (not_isZero_etaleStalk_iff_exists_mem_supportSection B S hS G t).1 hnz
  obtain ⟨Y, f, ⟨a, hab⟩, q', hq'⟩ := geometricPointFiber_jointly_surjective B S hS t
    (Presheaf.imageSieve φ.hom b) (Presheaf.imageSieve_mem _ φ.hom b) q
  refine (not_isZero_etaleStalk_iff_exists_mem_supportSection B S hS F t).2 ⟨Y, q', a, ?_⟩
  have hgerm : etaleGerm B S hS t (G.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v}) W q
      (ULift.up b) ≠ 0 := fun h =>
    hb ((etaleGerm_ulift_eq_zero_iff_mem_zeroOpen B S hS G t W q b).1 h)
  have hGa : q'.1.base default ∈ supportSection B S hS G Y (φ.hom.app (op Y) a) := by
    rw [hab]
    show q'.1.base default ∉
      (zeroOpen B S hS G Y (G.obj.map f.op b) :
        Set ((SmallEtale.toScheme B S hS).obj Y))
    intro hmem
    refine hgerm ?_
    rw [← etaleGerm_map B S hS t (G.obj ⋙ AddCommGrpCat.uliftFunctor.{u, v}) f q q' hq'
      (ULift.up b)]
    exact (etaleGerm_ulift_eq_zero_iff_mem_zeroOpen B S hS G t Y q'
      (G.obj.map f.op b)).2 hmem
  exact supportSection_map_subset B S hS F G φ Y a hGa

/-- **Stacks 04FT, part (6).** If a map of abelian sheaves on the small étale site is injective,
then the support of its source is contained in the support of its target. -/
@[stacks 04FT "part (6)"]
public theorem supportSheaf_subset_of_injective (φ : F ⟶ G)
    (hφ : ∀ U, Function.Injective (φ.hom.app U)) :
    AlgebraicGeometry.supportSheaf B S hS F ⊆ AlgebraicGeometry.supportSheaf B S hS G := by
  have hle : ∀ (U : SmallEtale B S hS) (a : F.obj.obj (op U)),
      zeroOpen B S hS G U (φ.hom.app (op U) a) ≤ zeroOpen B S hS F U a := by
    intro U a
    apply sSup_le
    rintro W ⟨V, f, hf, hW, hs⟩
    show (W : Set ((SmallEtale.toScheme B S hS).obj U)) ⊆
      (zeroOpen B S hS F U a : Set _)
    rw [hW]
    refine (@map_eq_zero_iff_le_zeroOpen B S hS F U a V f hf).mp (hφ (op V) ?_)
    calc φ.hom.app (op V) (F.obj.map f.op a)
        = G.obj.map f.op (φ.hom.app (op U) a) :=
          ConcreteCategory.congr_hom (φ.hom.naturality f.op) a
      _ = 0 := hs
      _ = φ.hom.app (op V) 0 := (map_zero _).symm
  rintro x ⟨t, htx, hnz⟩
  refine ⟨t, htx, ?_⟩
  obtain ⟨W, q, a, ha⟩ :=
    (not_isZero_etaleStalk_iff_exists_mem_supportSection B S hS F t).1 hnz
  exact (not_isZero_etaleStalk_iff_exists_mem_supportSection B S hS G t).2
    ⟨W, q, φ.hom.app (op W) a, fun hmem => ha (hle W a hmem)⟩

/-- **Stacks Project, Tag 04FT.** Let `S` be a scheme, let `F` be an abelian sheaf on the small
étale site of `S`, let `U` be an object of that site and let `σ ∈ F(U)`. Then

1. the support of `σ` is closed in `U`;
2. the support of `σ + σ'` is contained in the union of the supports of `σ` and `σ'`, for every
   `σ' ∈ F(U)`;
3. for every map `φ : F ⟶ G` of abelian sheaves on the site, the support of `φ(σ)` is contained
   in the support of `σ`;
4. the support of `F` is the union of the images in `S` of the supports of all local sections
   of `F`;
5. if `φ : F ⟶ G` is surjective then the support of `G` is contained in the support of `F`;
6. if `φ : F ⟶ G` is injective then the support of `F` is contained in the support of `G`,

the support of a section being `AlgebraicGeometry.SmallEtale.supportSection` of Stacks 04FS and
the support of a sheaf being `AlgebraicGeometry.supportSheaf`.

This is the whole tag in one statement, under exactly the source's hypotheses: nothing beyond the
site, the sheaf, the object and the section is assumed, and the further sheaf `G` and map `φ` of
parts (3), (5) and (6) are quantified where the source introduces them. Surjectivity in part (5)
is local surjectivity, `CategoryTheory.Sheaf.IsLocallySurjective`, which is what makes a map of
abelian sheaves an epimorphism; injectivity in part (6) is injectivity on every group of sections.
Each part is proved by the theorem of this chapter that states it alone:
`AlgebraicGeometry.SmallEtale.isClosed_supportSection`,
`AlgebraicGeometry.SmallEtale.supportSection_add_subset` and
`AlgebraicGeometry.SmallEtale.supportSection_map_subset`, in
`StacksFrontier.AlgebraicGeometry.Etale.SupportSections`, for parts (1), (2) and (3); and
`AlgebraicGeometry.supportSheaf_eq_iUnion_image_supportSection`,
`AlgebraicGeometry.supportSheaf_subset_of_isLocallySurjective` and
`AlgebraicGeometry.supportSheaf_subset_of_injective`, above, for parts (4), (5) and (6). Those six
registrations are retained, each stating its own part of the tag. -/
@[stacks 04FT]
public theorem isClosed_supportSection_and_supportSheaf_eq_iUnion_image_supportSection_and_subset
    (U : SmallEtale B S hS) (σ : F.obj.obj (op U)) :
    IsClosed (supportSection B S hS F U σ) ∧
      (∀ σ' : F.obj.obj (op U), supportSection B S hS F U (σ + σ') ⊆
        supportSection B S hS F U σ ∪ supportSection B S hS F U σ') ∧
      (∀ φ : F ⟶ G, supportSection B S hS G U (φ.hom.app (op U) σ) ⊆
        supportSection B S hS F U σ) ∧
      (AlgebraicGeometry.supportSheaf B S hS F =
        ⋃ (V : SmallEtale B S hS), ⋃ (a : F.obj.obj (op V)),
          (B.inclusion.map V.obj.hom).base '' supportSection B S hS F V a) ∧
      (∀ φ : F ⟶ G, Sheaf.IsLocallySurjective φ →
        AlgebraicGeometry.supportSheaf B S hS G ⊆ AlgebraicGeometry.supportSheaf B S hS F) ∧
      (∀ φ : F ⟶ G, (∀ V, Function.Injective (φ.hom.app V)) →
        AlgebraicGeometry.supportSheaf B S hS F ⊆ AlgebraicGeometry.supportSheaf B S hS G) :=
  ⟨isClosed_supportSection B S hS F U σ,
    fun σ' ↦ supportSection_add_subset B S hS F U σ σ',
    fun φ ↦ supportSection_map_subset B S hS F G φ U σ,
    supportSheaf_eq_iUnion_image_supportSection B S hS F,
    fun φ hφ ↦ @supportSheaf_subset_of_isLocallySurjective B S hS F G φ hφ,
    fun φ ↦ supportSheaf_subset_of_injective B S hS F G φ⟩

end AlgebraicGeometry

end
