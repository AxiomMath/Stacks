module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits

/-!
# Characterization of affine formal algebraic spaces (Stacks 0AIB)

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a sheaf of sets on the big
fppf site of `S`. **Stacks 0AIB** characterizes the affine formal algebraic spaces among such
sheaves: `X` is an affine formal algebraic space if and only if

1. every morphism `U ⟶ X` out of a sheaf represented by an affine scheme over `S` factors as
   `U ⟶ T ⟶ X` with `T` an affine scheme over `S` and `T ⟶ X` representable by schemes and a
   thickening, and
2. `X` satisfies the set-theoretic condition of Stacks 0AIS.

The forward implication is the content of Stacks 0AIA and Stacks 0AI9: a presentation of `X` as
a directed colimit of affine thickening stages lets every morphism out of a quasi-compact
algebraic space -- in particular out of a sheaf represented by an affine scheme -- factor
through a stage, and each stage maps to `X` representably and by a thickening.

The converse builds the presentation out of the factorizations themselves. The *thickening
stages* of `X` are the pairs consisting of an affine object `T` of the site and a morphism
`T ⟶ X` which is representable and a thickening; a stage map is a monomorphism, so there is at
most one morphism of stages between two stages and the thickening stages form a preordered
class with a forgetful functor to the affine objects of the site. Condition (1) applied to the
coproduct of two stages makes that preorder directed, and applied to a stage alone it shows the
colimit of the forgetful functor is `X`: sections of the filtered colimit over an object of the
site are sections of a single stage, which is exactly a factorization through one stage. The
preorder is nonempty because the empty affine scheme is a stage.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_iff`: **Stacks 0AIB**.

## Implementation notes

An affine scheme over `S` is an object of the full subcategory
`AlgebraicGeometry.BigAffineFppf` of affine objects of the big fppf site of `S`, and a morphism
from it to `X` is a morphism out of `CategoryTheory.Sheaf.sheafifiedYoneda` of that object, so
the statement does not presuppose that the site is subcanonical. Being a thickening into `X` is
the relative morphism property of `Stacks.Thickenings.IsThickening` pulled back along
`AlgebraicGeometry.BigFppfOver.toScheme`; representability is recorded separately because that
is the form in which consumers use it, matching Stacks 0AI9.

Subcanonicity of the topology is *not* reproved: `AlgebraicGeometry.bigFppfOver_subcanonical`
is available and is used directly. Likewise the quasi-compactness of a sheaf represented by an
affine object of the site is `AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_obj`, and the
empty affine stage is built from `AlgebraicGeometry.BigFppfOver.initialObj`.

The indexing class of the constructed presentation is the class of thickening stages, which
lives in `Type (u + 1)` as the predicate of Stacks 0AI7 requires; its preorder is supplied as
an explicit witness rather than an instance, again as that predicate requires.

## References

* [Stacks Project, Tag 0AIB](https://stacks.math.columbia.edu/tag/0AIB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The empty sieve covers an object of a big fppf site whose underlying scheme is empty: the
empty family is an fppf covering of the empty scheme. -/
private theorem bot_mem_topology_of_isEmpty (B : BigFppfSite.{u})
    {T : B.Schemes} (hT : IsEmpty (B.inclusion.obj T)) :
    (⊥ : Sieve T) ∈ B.topology T := by
  let E : PreZeroHypercover.{u + 1} T := PreZeroHypercover.empty T
  have hfp : IsFppfCovering ⟨T, E⟩ := by
    rw [IsFppfCovering, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_empty,
      Presieve.map_bot]
    exact Scheme.bot_mem_precoverage
      (@Flat ⊓ @LocallyOfFinitePresentation) (B.inclusion.obj T)
  simpa [E, PreZeroHypercover.presieve₀, PreZeroHypercover.sieve₀] using
    B.generate_mem_topology_of_isFppfCovering E hfp

/-- The empty sieve covers an object of the big fppf category over `S` whose underlying scheme
is empty. -/
private theorem bot_mem_topologyOver_of_isEmpty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj V)) :
    (⊥ : Sieve V) ∈ BigFppfOver.topology B S hS V := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff]
  simpa using bot_mem_topology_of_isEmpty B hV

/-- A sheaf has at most one section over an object of the big fppf category over `S` whose
underlying scheme is empty, since the empty sieve covers that object. -/
private theorem subsingleton_sections_of_isEmpty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (V : BigFppfOver B S hS)
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj V)) :
    Subsingleton (X.obj.obj (op V)) := by
  have hsh := (isSheaf_iff_isSheaf_of_type
    (J := BigFppfOver.topology B S hS) X.obj).1 X.property
  exact ⟨fun _ _ => (hsh ⊥ (bot_mem_topologyOver_of_isEmpty B S hS V hV)).isSeparatedFor.ext
    (by rintro _ _ ⟨⟩)⟩

/-- Descent of morphisms into a sheaf along a covering family: a compatible family of morphisms
out of the sheafified representables of the members of a covering family of `V` descends to a
morphism out of the sheafified representable of `V`. -/
private theorem exists_desc_of_covering_family
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {I : Type (u + 1)} {V : C} (U : I → C) (f : ∀ i, U i ⟶ V)
    (hcov : Sieve.ofArrows U f ∈ J V)
    (X : Sheaf J (Type (u + 1)))
    (a : ∀ i, (Sheaf.sheafifiedYoneda J).obj (U i) ⟶ X)
    (hcompat : ∀ ⦃W : C⦄ (i j : I) (b : W ⟶ U i) (c : W ⟶ U j),
      b ≫ f i = c ≫ f j →
      (Sheaf.sheafifiedYoneda J).map b ≫ a i =
        (Sheaf.sheafifiedYoneda J).map c ≫ a j) :
    ∃ t : (Sheaf.sheafifiedYoneda J).obj V ⟶ X,
      ∀ i, (Sheaf.sheafifiedYoneda J).map (f i) ≫ t = a i := by
  let x (i : I) : PUnit.{u + 2} ⟶ X.obj.obj (op (U i)) :=
    TypeCat.ofHom (fun _ ↦ Sheaf.sectionEquiv J (a i))
  have hx : ∀ ⦃W : C⦄ ⦃i j : I⦄ (b : W ⟶ U i) (c : W ⟶ U j),
      b ≫ f i = c ≫ f j → x i ≫ X.obj.map b.op = x j ≫ X.obj.map c.op := by
    intro W i j b c h
    ext z
    exact (Sheaf.sectionEquiv_map_comp J b (a i)).symm.trans
      ((congrArg (Sheaf.sectionEquiv J) (hcompat i j b c h)).trans
        (Sheaf.sectionEquiv_map_comp J c (a j)))
  let t := X.property.amalgamateOfArrows f hcov x hx
  refine ⟨(Sheaf.sectionEquiv J).symm (t PUnit.unit),
    fun i ↦ (Sheaf.sectionEquiv J).injective ?_⟩
  rw [Sheaf.sectionEquiv_map_comp, Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    (X.property.amalgamateOfArrows_map f hcov x hx i) PUnit.unit

/-- A family of morphisms of the big fppf category over `S` which are flat, locally of finite
presentation and jointly surjective on underlying schemes generates a covering sieve. -/
private theorem sieve₀_mem_topology_of_flat (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {Z : BigFppfOver B S hS}
    (E : PreZeroHypercover.{u + 1} Z)
    (hsurj : ∀ z : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ k y, (BigFppfOver.toScheme B S hS).map (E.f k) y = z)
    (hfl : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (E.f k)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (E.f k))) :
    E.sieve₀ ∈ BigFppfOver.topology B S hS Z := by
  have hE : IsFppfCovering
      ⟨(BigFppfOver.forget B S hS).obj Z, E.map (BigFppfOver.forget B S hS)⟩ := by
    rw [IsFppfCovering, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀,
      Presieve.map_ofArrows]
    exact (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, hfl⟩
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    PreZeroHypercover.sieve₀, Sieve.overEquiv_ofArrows]
  exact B.generate_mem_topology_of_isFppfCovering _ hE

/-- Descent of morphisms into a sheaf along a covering family of the big fppf category over `S`
whose members are monomorphisms with pairwise disjoint ranges on underlying schemes: no
compatibility is needed, since two members either agree or are jointly dominated only by empty
objects. -/
private theorem exists_desc_of_disjoint_cover (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {Z : BigFppfOver B S hS}
    (E : PreZeroHypercover.{u + 1} Z) (hcov : E.sieve₀ ∈ BigFppfOver.topology B S hS Z)
    (hmono : ∀ k, Mono ((BigFppfOver.toScheme B S hS).map (E.f k)))
    (hdisj : Pairwise fun k l ↦ Disjoint
      (Set.range ((BigFppfOver.toScheme B S hS).map (E.f k)))
      (Set.range ((BigFppfOver.toScheme B S hS).map (E.f l))))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (a : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (E.X k) ⟶ X) :
    ∃ t : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z ⟶ X,
      ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (E.f k) ≫ t = a k := by
  let H := BigFppfOver.toScheme B S hS
  refine exists_desc_of_covering_family _ E.X E.f hcov X a fun T k l c d h ↦ ?_
  by_cases hkl : k = l
  · subst hkl
    have := H.mono_of_mono_map (hmono k)
    obtain rfl := (cancel_mono (E.f k)).1 h
    rfl
  · have hw : H.map c ≫ H.map (E.f k) = H.map d ≫ H.map (E.f l) := by
      rw [← H.map_comp, h, H.map_comp]
    have := subsingleton_sections_of_isEmpty B S hS X T
      (Scheme.isEmpty_of_commSq (CommSq.mk hw) (hdisj hkl))
    exact (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective (Subsingleton.elim _ _)

/-- Two affine schemes over `S` are jointly dominated by a third: their coproduct is again an
affine scheme over `S`, the two inclusions form an fppf covering of it, and so a pair of
morphisms into a sheaf out of the two sheafified representables descends to the coproduct.

The compatibility needed for the descent is automatic: the two inclusions are monomorphisms
with disjoint ranges, so a pair of morphisms into the coproduct either agrees or has empty
source, and a sheaf has at most one section over an empty object. -/
private theorem exists_affine_coproduct_desc (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U V : BigAffineFppf B S hS) :
    ∃ (W : BigAffineFppf B S hS) (i : U ⟶ W) (j : V ⟶ W),
      ∀ (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
        (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U.obj ⟶ X)
        (b : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V.obj ⟶ X),
        ∃ t : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W.obj ⟶ X,
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map i.hom ≫ t = a ∧
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j.hom ≫ t = b := by
  classical
  let UO := (BigAffineFppf.inclusion B S hS).obj U
  let VO := (BigAffineFppf.inclusion B S hS).obj V
  let U0 := (BigFppfOver.forget B S hS).obj UO
  let V0 := (BigFppfOver.forget B S hS).obj VO
  let A := B.inclusion.obj U0
  let C := B.inclusion.obj V0
  let Z : Scheme.{u} := A ⨿ C
  let Z0 : B.Schemes := ⟨Z, B.contains_coprod U0.property V0.property⟩
  let q : Z0 ⟶ B.obj hS := B.inclusion.preimage
    (show B.inclusion.obj Z0 ⟶ B.inclusion.obj (B.obj hS) from
      coprod.desc (B.inclusion.map UO.hom) (B.inclusion.map VO.hom))
  let ZO : BigFppfOver B S hS := Over.mk q
  have hq : B.inclusion.map q =
      coprod.desc (B.inclusion.map UO.hom) (B.inclusion.map VO.hom) :=
    B.inclusion.map_preimage _
  have mk : ∀ (W' : BigFppfOver B S hS) (m : B.inclusion.obj W'.left ⟶ Z),
      m ≫ B.inclusion.map q = B.inclusion.map W'.hom →
        ∃ o : W' ⟶ ZO, (BigFppfOver.toScheme B S hS).map o = m := fun W' m hm ↦
    ⟨Over.homMk (B.inclusion.preimage m) (B.inclusion.map_injective
      (by rw [Functor.map_comp, B.inclusion.map_preimage]; exact hm)),
      B.inclusion.map_preimage _⟩
  obtain ⟨iO, hi⟩ := mk UO coprod.inl (by rw [hq, coprod.inl_desc])
  obtain ⟨jO, hj⟩ := mk VO coprod.inr (by rw [hq, coprod.inr_desc])
  have : IsAffine A := U.property
  have : IsAffine C := V.property
  have hZaff : IsAffine (A ⨿ C) := by infer_instance
  refine ⟨⟨ZO, hZaff⟩, ObjectProperty.homMk iO, ObjectProperty.homMk jO, fun X a b ↦ ?_⟩
  let H := BigFppfOver.toScheme B S hS
  let E : PreZeroHypercover.{u + 1} ZO :=
    ⟨PUnit.{u + 2} ⊕ PUnit.{u + 2},
      fun k ↦ k.elim (fun _ ↦ UO) (fun _ ↦ VO),
      fun k ↦ k.rec (fun _ ↦ iO) (fun _ ↦ jO)⟩
  have hP : ∀ k, Mono (H.map (E.f k)) ∧ Flat (H.map (E.f k)) ∧
      LocallyOfFinitePresentation (H.map (E.f k)) := by
    rintro (k | k)
    · change Mono (H.map iO) ∧ Flat (H.map iO) ∧ LocallyOfFinitePresentation (H.map iO)
      rw [hi]
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    · change Mono (H.map jO) ∧ Flat (H.map jO) ∧ LocallyOfFinitePresentation (H.map jO)
      rw [hj]
      exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hcov : E.sieve₀ ∈ BigFppfOver.topology B S hS ZO := by
    refine sieve₀_mem_topology_of_flat B S hS E (fun z ↦ ?_) ?_
    · obtain ⟨k | k, y, hy⟩ := (coprodOpenCover.{u, u + 1} A C).exists_eq z
      · dsimp only [coprodOpenCover] at y hy
        exact ⟨Sum.inl k, y, by
          change (H.map iO) y = z
          rwa [hi]⟩
      · dsimp only [coprodOpenCover] at y hy
        exact ⟨Sum.inr k, y, by
          change (H.map jO) y = z
          rwa [hj]⟩
    · exact fun k ↦ (hP k).2
  have hmono : ∀ k, Mono (H.map (E.f k)) := fun k ↦ (hP k).1
  have hdisj : Disjoint (Set.range (H.map iO)) (Set.range (H.map jO)) := by
    rw [hi, hj]
    exact (isCompl_range_inl_inr A C).disjoint
  obtain ⟨t, ht⟩ := exists_desc_of_disjoint_cover B S hS E hcov hmono
    (by rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) hkl <;> first | exact absurd rfl hkl | exact hdisj |
      exact hdisj.symm) X (fun k ↦ k.rec (fun _ ↦ a) (fun _ ↦ b))
  exact ⟨t, ht (.inl PUnit.unit), ht (.inr PUnit.unit)⟩

/-- Two affine schemes over `S` are jointly dominated by a third: their coproduct is again an
affine scheme over `S`, the two inclusions form an fppf covering of it, and so a pair of
morphisms into a sheaf out of the two sheafified representables descends to the coproduct.

The compatibility needed for the descent is automatic: the two inclusions are monomorphisms
with disjoint ranges, so a pair of morphisms into the coproduct either agrees or has empty
source, and a sheaf has at most one section over an empty object. -/
alias exists_affine_coproduct_desc' := exists_affine_coproduct_desc

/-- A *thickening stage* of a sheaf `X` on the big fppf site of `S` is an affine scheme `T`
over `S` together with a morphism `T ⟶ X` which is representable by objects of the site and
whose every represented base change is a thickening of schemes.

These are the objects out of which a presentation of `X` as an affine formal algebraic space is
assembled in **Stacks 0AIB**. -/
private structure ThickeningStage (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) where
  /-- The affine scheme over `S` carrying the stage. -/
  U : BigAffineFppf B S hS
  /-- The morphism from the sheaf represented by the stage to `X`. -/
  f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj U) ⟶ X
  /-- The stage morphism is representable by objects of the site. -/
  relativelyRepresentable :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f
  /-- Every represented base change of the stage morphism is a thickening of schemes. -/
  isThickening :
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f

/-- The morphism of a thickening stage to `X` is a monomorphism: its base change along itself
is a thickening, hence a monomorphism, and a split epimorphism, hence an isomorphism. -/
private theorem ThickeningStage.mono_map {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (A : ThickeningStage B S hS X) : Mono A.f := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let hf := A.relativelyRepresentable
  let hpb := hf.isPullback A.f
  let p := F.map (hf.snd A.f)
  have hpThick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (hf.snd A.f)) :=
    A.isThickening.property A.f (hf.fst A.f) (hf.snd A.f) hpb
  have hpScheme : Mono ((BigFppfOver.toScheme B S hS).map (hf.snd A.f)) :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mp hpThick.1 |>.2
  have : Mono (hf.snd A.f) := by
    have : Mono (hf.snd A.f).left :=
      B.inclusion.mono_of_mono_map (f := (hf.snd A.f).left) hpScheme
    exact Over.mono_of_mono_left (hf.snd A.f)
  have hpSheaf : Mono p := by
    have : PreservesLimitsOfShape WalkingCospan F := by
      dsimp [F, Sheaf.sheafifiedYoneda]
      infer_instance
    exact Functor.map_mono F (hf.snd A.f)
  let δ := hpb.lift (𝟙 _) (𝟙 _) (by simp)
  have hδ₁ : δ ≫ hf.fst A.f = 𝟙 _ := hpb.lift_fst _ _ _
  have hδ₂ : δ ≫ p = 𝟙 _ := hpb.lift_snd _ _ _
  have : IsSplitEpi p := IsSplitEpi.mk' ⟨δ, hδ₂⟩
  have : IsIso p := isIso_of_mono_of_isSplitEpi p
  have : IsIso δ := by
    rw [IsIso.eq_inv_of_inv_hom_id hδ₂]
    infer_instance
  refine ⟨fun a b hab ↦ ?_⟩
  let r := hpb.lift a b hab
  calc
    a = r ≫ hf.fst A.f := (hpb.lift_fst a b hab).symm
    _ = r ≫ p := by rw [(cancel_epi δ).1 (hδ₁.trans hδ₂.symm)]
    _ = b := hpb.lift_snd a b hab

/-- One thickening stage *refines* another when the first factors through the second over
`X`. -/
private def ThickeningStage.le {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (A C : ThickeningStage B S hS X) : Prop :=
  ∃ g : A.U ⟶ C.U,
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map g) ≫ C.f = A.f

/-- The chosen factorization of one thickening stage through a stage refining it. -/
private noncomputable def ThickeningStage.factor {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {A C : ThickeningStage B S hS X} (h : ThickeningStage.le A C) : A.U ⟶ C.U :=
  Classical.choose h

/-- The chosen factorization is a factorization over `X`. -/
private theorem ThickeningStage.factor_spec {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {A C : ThickeningStage B S hS X} (h : ThickeningStage.le A C) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (A.factor h)) ≫ C.f = A.f :=
  Classical.choose_spec h

/-- The chosen factorization between two thickening stages is a thickening of affine schemes:
the stage morphism of the target is a monomorphism, so the factorization exhibits the source
stage as a base change of the target stage along itself. -/
private theorem ThickeningStage.factor_isThickening
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {A C : ThickeningStage B S hS X} (h : ThickeningStage.le A C) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (A.factor h)) := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : Mono C.f := C.mono_map
  have hpull : IsPullback (𝟙 (F.obj
        ((BigAffineFppf.inclusion B S hS).obj A.U)))
      (F.map ((BigAffineFppf.inclusion B S hS).map (A.factor h)))
      A.f C.f :=
    IsPullback.of_horiz_isIso_mono ⟨by
      simpa only [Category.id_comp] using (A.factor_spec h).symm⟩
  change Stacks.Thickenings.IsThickening
    ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (A.factor h)))
  exact A.isThickening.property C.f (𝟙 _) _ hpull

/-- Refinement of thickening stages is a preorder. -/
@[instance_reducible]
private def thickeningStagePreorder (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :
    Preorder (ThickeningStage B S hS X) where
  le := ThickeningStage.le
  le_refl A := ⟨𝟙 _, by
    rw [(BigAffineFppf.inclusion B S hS).map_id,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_id, Category.id_comp]⟩
  le_trans A C D hAC hCD := by
    obtain ⟨g, hg⟩ := hAC
    obtain ⟨h, hh⟩ := hCD
    refine ⟨g ≫ h, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hh, hg]

attribute [local instance] thickeningStagePreorder

/-- There is at most one factorization of one thickening stage through another: the stage
morphism of the target is a monomorphism and sheafified Yoneda is faithful. -/
private theorem ThickeningStage.hom_eq_of_factor
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {A C : ThickeningStage B S hS X} {f g : A.U ⟶ C.U}
    (hf : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map f) ≫ C.f = A.f)
    (hg : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map g) ≫ C.f = A.f) : f = g := by
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have : Mono C.f := C.mono_map
  exact (BigAffineFppf.inclusion B S hS).map_injective <|
    (Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)).map_injective
      ((cancel_mono C.f).1 (hf.trans hg.symm))

/-- The directed system of thickening stages: a stage is sent to its affine scheme over `S`
and a refinement to the chosen factorization. -/
private noncomputable def thickeningStageDiagram (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :
    ThickeningStage B S hS X ⥤ BigAffineFppf B S hS := by
  refine
    { obj := ThickeningStage.U
      map := fun {A C} h => A.factor (leOfHom h)
      map_id := ?_
      map_comp := ?_ }
  · intro A
    apply ThickeningStage.hom_eq_of_factor
    · exact A.factor_spec (le_rfl : A ≤ A)
    · simpa using (Category.id_comp A.f)
  · intro A C D hAC hCD
    refine (ThickeningStage.hom_eq_of_factor
      (f := A.factor (leOfHom hAC) ≫ C.factor (leOfHom hCD))
      (g := A.factor (leOfHom (hAC ≫ hCD))) ?_ ?_).symm
    · simp only [Functor.map_comp, Category.assoc]
      rw [C.factor_spec (leOfHom hCD), A.factor_spec (leOfHom hAC)]
    · exact A.factor_spec (leOfHom (hAC ≫ hCD))

/-- Any two thickening stages are refined by a third, granted the factorization property: the
coproduct of the two affine schemes receives both stage morphisms, and a factorization of the
resulting morphism gives a stage refining both. -/
private theorem ThickeningStage.exists_upper_bound
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hfactor : ∀ (U : BigAffineFppf B S hS)
      (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj U) ⟶ X),
      ∃ (T : BigAffineFppf B S hS)
        (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj U) ⟶
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
              ((BigAffineFppf.inclusion B S hS).obj T))
        (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X),
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).relativelyRepresentable h ∧
        (MorphismProperty.relative (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS))
          (MorphismProperty.inverseImage
            (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) h ∧ g ≫ h = f)
    (A C : ThickeningStage B S hS X) :
    ∃ D : ThickeningStage B S hS X,
      ThickeningStage.le A D ∧ ThickeningStage.le C D := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := BigAffineFppf.inclusion B S hS ⋙ F
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : F.Full := Sheaf.sheafifiedYoneda_full J
  obtain ⟨W, i, j, hext⟩ := exists_affine_coproduct_desc B S hS A.U C.U
  obtain ⟨f₀, hf₀i, hf₀j⟩ := hext X A.f C.f
  obtain ⟨T, g, h, hrep, hthick, hfac⟩ := hfactor W f₀
  let D : ThickeningStage B S hS X := ⟨T, h, hrep, hthick⟩
  have key : ∀ {U' : BigAffineFppf B S hS} (k : U' ⟶ W) (f' : F.obj
      ((BigAffineFppf.inclusion B S hS).obj U') ⟶ X), K.map k ≫ f₀ = f' →
      ∃ a : U' ⟶ T, F.map ((BigAffineFppf.inclusion B S hS).map a) ≫ D.f = f' := by
    intro U' k f' hk
    refine ⟨(BigAffineFppf.inclusion B S hS).preimage (F.preimage (K.map k ≫ g)), ?_⟩
    change _ ≫ h = _
    rw [(BigAffineFppf.inclusion B S hS).map_preimage, F.map_preimage, Category.assoc, hfac]
    exact hk
  exact ⟨D, key i A.f hf₀i, key j C.f hf₀j⟩

/-- The cocone on the directed system of thickening stages whose point is `X` and whose
components are the stage morphisms. -/
private noncomputable def thickeningStageCocone
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :
    Cocone (thickeningStageDiagram B S hS X ⋙
      BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) where
  pt := X
  ι :=
    { app := fun A ↦ A.f
      naturality := fun A C h ↦ by
        change _ ≫ C.f = A.f ≫ 𝟙 X
        rw [Category.comp_id]
        exact A.factor_spec (leOfHom h) }

/-- If every morphism to `X` out of a sheaf represented by an affine scheme over `S` factors
through a thickening stage, and the thickening stages are directed, then `X` is the colimit of
the directed system of thickening stages: over each object of the site, the factorizations make
every section of `X` come from a single stage, and stage morphisms are monomorphisms, so
sections coming from two stages already agree on a common refinement. -/
private noncomputable def thickeningStageCoconeIsColimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hdir : IsDirected (ThickeningStage B S hS X) (· ≤ ·))
    (hfac : ∀ (U : BigAffineFppf B S hS)
      (f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U.obj ⟶ X),
      ∃ (A : ThickeningStage B S hS X)
        (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U.obj ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj A.U.obj),
        g ≫ A.f = f) : IsColimit (thickeningStageCocone B S hS X) := by
  let J := BigFppfOver.topology B S hS
  let JA := BigAffineFppf.topology B S hS
  let R := (BigAffineFppf.inclusion B S hS).sheafPushforwardContinuous
    (Type (u + 1)) JA J
  apply isColimitOfReflects R
  apply isColimitOfReflects (sheafToPresheaf JA (Type (u + 1)))
  apply evaluationJointlyReflectsColimits
  intro U
  apply Types.FilteredColimit.isColimitOf
  · intro x
    obtain ⟨A, g, hg⟩ := hfac U.unop ((Sheaf.sectionEquiv J).symm x)
    refine ⟨A, Sheaf.sectionEquiv J g, ?_⟩
    change x = A.f.hom.app (op U.unop.obj) (Sheaf.sectionEquiv J g)
    exact ((Sheaf.sectionEquiv J).apply_symm_apply x).symm.trans
      ((congrArg (Sheaf.sectionEquiv J) hg.symm).trans
        (Sheaf.sectionEquiv_comp J g A.f))
  · intro A C x y hxy
    obtain ⟨D, hAD, hCD⟩ := hdir.directed A C
    refine ⟨D, homOfLE hAD, homOfLE hCD, ?_⟩
    let E := ((sheafToPresheaf J (Type (u + 1))) ⋙
      (evaluation _ (Type (u + 1))).obj (op U.unop.obj))
    have : Mono D.f := D.mono_map
    apply ((CategoryTheory.mono_iff_injective (E.map D.f)).mp inferInstance)
    have hA := ConcreteCategory.congr_hom
      (congrArg E.map (A.factor_spec hAD)) x
    have hC := ConcreteCategory.congr_hom
      (congrArg E.map (C.factor_spec hCD)) y
    convert hA.trans (hxy.trans hC.symm) using 1 <;>
      simp [E, R, thickeningStageDiagram] <;> rfl

/-- The empty scheme is an affine scheme over `S`. -/
private theorem exists_empty_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    ∃ U : BigAffineFppf B S hS,
      IsEmpty ((BigAffineFppf.toScheme B S hS).obj U) := by
  have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj
      (BigFppfOver.initialObj B S hS)) :=
    inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  exact ⟨⟨_, @isAffine_of_isEmpty _ hempty⟩, hempty⟩

/-- **Stacks 0AIB.** A sheaf on the big fppf site of `S` is an affine formal algebraic space if
and only if every morphism to it from a sheaf represented by an affine scheme over `S` factors
through a morphism from an affine scheme over `S` which is representable and a thickening, and
the sheaf satisfies the set-theoretic condition of Stacks 0AIS. -/
@[stacks 0AIB]
theorem isAffineFormalAlgebraicSpace_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :
    IsAffineFormalAlgebraicSpace B S hS X ↔
      ((∀ U : BigAffineFppf B S hS,
          ∀ f : (Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).obj
              ((BigAffineFppf.inclusion B S hS).obj U) ⟶ X,
          ∃ T : BigAffineFppf B S hS,
            ∃ g : (Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)).obj
                ((BigAffineFppf.inclusion B S hS).obj U) ⟶
              (Sheaf.sheafifiedYoneda
                (BigFppfOver.topology B S hS)).obj
                  ((BigAffineFppf.inclusion B S hS).obj T),
            ∃ h : (Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)).obj
                ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X,
              (Sheaf.sheafifiedYoneda
                (BigFppfOver.topology B S hS)).relativelyRepresentable h ∧
              (MorphismProperty.relative
                (Sheaf.sheafifiedYoneda
                  (BigFppfOver.topology B S hS))
                (MorphismProperty.inverseImage
                  (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
                  (BigFppfOver.toScheme B S hS))) h ∧
              g ≫ h = f) ∧
        SatisfiesSetTheoreticCondition B S hS X) := by
  constructor
  · rintro ⟨hset, I, pre, hI, hdir, D, hD, ⟨e⟩⟩
    let : Preorder I := pre
    have : Nonempty I := hI
    have : IsDirected I (· ≤ ·) := hdir
    refine ⟨fun U f ↦ ?_, hset⟩
    let V := (BigAffineFppf.inclusion B S hS).obj U
    let Y := yoneda.obj V
    have hYqc : Space.IsQuasiCompactSpace B S hS Y := by
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := U.property
      exact Space.isQuasiCompactSpace_yoneda_obj B S hS (U := V) inferInstance
    let F := D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
    let e' : colimit F ≅ X := e.symm
    obtain ⟨i, g, hg⟩ := exists_factor_through_thickening'
      B S hS I D (fun _ _ g ↦ (hD g).1) X e Y hYqc f
    exact ⟨D.obj i, g, colimit.ι F i ≫ e'.hom,
      relativelyRepresentable_colimitι B S hS (D := D) (hD := hD) (X := X) (e := e') i,
      isThickening_colimitι B S hS (D := D) (hD := hD) (X := X) (e := e') i, hg⟩
  · rintro ⟨hfactor, hset⟩
    let J := BigFppfOver.topology B S hS
    have hfac : ∀ (U : BigAffineFppf B S hS)
        (f : (Sheaf.sheafifiedYoneda J).obj U.obj ⟶ X),
        ∃ (A : ThickeningStage B S hS X)
          (g : (Sheaf.sheafifiedYoneda J).obj U.obj ⟶
            (Sheaf.sheafifiedYoneda J).obj A.U.obj), g ≫ A.f = f := by
      intro U f
      obtain ⟨T, g, h, hr, ht, he⟩ := hfactor U f
      exact ⟨⟨T, h, hr, ht⟩, g, he⟩
    have hdir : IsDirected (ThickeningStage B S hS X) (· ≤ ·) :=
      ⟨fun A C ↦ ThickeningStage.exists_upper_bound B S hS X hfactor A C⟩
    obtain ⟨U, hU⟩ := exists_empty_affine B S hS
    let z := (Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover X U.obj
      (bot_mem_topologyOver_of_isEmpty B S hS U.obj hU))).default
    obtain ⟨A, -, -⟩ := hfac U ((Sheaf.sectionEquiv J).symm z)
    exact ⟨hset, ThickeningStage B S hS X, thickeningStagePreorder B S hS X,
      ⟨A⟩, hdir, thickeningStageDiagram B S hS X,
      fun A C h ↦ ThickeningStage.factor_isThickening (leOfHom h),
      ⟨(thickeningStageCoconeIsColimit B S hS X hdir hfac).coconePointUniqueUpToIso
        (colimit.isColimit _)⟩⟩

end AlgebraicGeometry.FormalSpace

end
