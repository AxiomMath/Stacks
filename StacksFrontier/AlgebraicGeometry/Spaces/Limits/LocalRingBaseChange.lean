module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change of an algebraic space to the local ring at a point of the base

Let `S` be a scheme and `s` a point of `S`. The affine open neighbourhoods of `s`, ordered by
reverse inclusion, form a directed set, and the local ring `𝒪_{S, s}` is the filtered colimit
of the rings `𝒪_S(U)` over that set. Dually `Spec(𝒪_{S, s})` is the cofiltered limit of the
affine opens `U` themselves, and this remains true in the big fppf site of `S`, where each `U`
is an object of the site and `Spec(𝒪_{S, s})` is the vertex of the limiting cone.

Base change along a morphism `f : X ⟶ *` from a presheaf on the site to the terminal presheaf
preserves connected limits, because it is `Over.pullback f` followed by the forgetful functor
of a slice category. Applying it to the cone above gives

    `X ×_S Spec(𝒪_{S, s}) = lim_U X ×_S U`,

which is the limit identity used in the proof of Stacks 0B80.

## Main results

* `AlgebraicGeometry.Scheme.AffineNhds`: the affine open neighbourhoods of a point of a scheme,
  ordered by reverse inclusion.
* `AlgebraicGeometry.Scheme.isLimitAffineNhdsSpecStalkCone`: `Spec(𝒪_{S, s})` is the limit of
  the affine open neighbourhoods of `s`.
* `AlgebraicGeometry.Space.isLimitAffineNhdsSiteConeOfStalkIso`: the same limit, taken in the big
  fppf site of `S`.
* `AlgebraicGeometry.Space.isLimitBaseChangeMapCone`: base change along a morphism to the
  terminal presheaf carries a limiting cone of objects of the site to a limiting cone of
  presheaves; in particular `X ×_S Spec(𝒪_{S, s}) = lim_U X ×_S U`.

## Implementation notes

The index category is `{U : (S.Opens)ᵒᵈ // IsAffineOpen U.ofDual ∧ s ∈ U.ofDual}`: the order
dual is taken so that the index set is *directed* — shrinking a neighbourhood is going up — and
so that the inverse system is a functor out of its opposite, which is the shape
`AlgebraicGeometry.Space.LimitSituation` (Situation 084R) asks for.

The identification of `Spec(𝒪_{S, s})` with the limit is `Scheme.Spec` applied to the colimit
of the sections functor over the open neighbourhoods of `s`, restricted along the inclusion of
the affine ones, which is final because the affine opens form a basis.

What is here is the part of Stacks 0B80 which is independent of Stacks 07SR. One further step
separates it from that tag, and it is not proved here: Stacks 07SR itself -- that a stage of a
limit situation is a scheme as soon as the limit is -- applied to the inverse system
`U ↦ X ×_S U` above; it yields an affine open neighbourhood `U` of `s` for which `X ×_S U` is a
scheme. Everything from there on is in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/LocalRingSchemeCriterion.lean`, which carries
Stacks 0B80 with Stacks 07SR as its only hypothesis. In particular the second step -- that an
algebraic space covered by open subspaces which are schemes is a scheme -- needs no size
hypothesis: Stacks 03JH holds in its unconditional form, as
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`
in `StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocusEquivalence.lean`, so the cofinal
family indexed below the cofinality of the site's cutoff that
`AlgebraicGeometry.Space.isRepresentable_schematicLocus` asks for is not needed.

## References

* [Stacks Project, Tag 0B80](https://stacks.math.columbia.edu/tag/0B80)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry

namespace Scheme

/-! ### Affine open neighbourhoods of a point -/

variable (S : Scheme.{u}) (s : S)

/-- The affine open neighbourhoods of a point `s` of a scheme `S`, ordered by reverse
inclusion: `U ≤ V` means `V ⊆ U`. With this order the index set is directed, the affine opens
being a basis of the topology. -/
abbrev AffineNhds : Type u :=
  {U : (S.Opens)ᵒᵈ // IsAffineOpen (OrderDual.ofDual U) ∧ s ∈ OrderDual.ofDual U}

namespace AffineNhds

variable {S s}

/-- The underlying open of an affine open neighbourhood. -/
abbrev opens (U : AffineNhds S s) : S.Opens := OrderDual.ofDual U.1

/-- For affine open neighbourhoods, `U ≤ V` holds if and only if `V ⊆ U` as opens. -/
theorem le_iff {U V : AffineNhds S s} : U ≤ V ↔ V.opens ≤ U.opens := Iff.rfl

variable (S s)

/-- Every point of a scheme has an affine open neighbourhood. -/
instance : Nonempty (AffineNhds S s) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (show s ∈ (⊤ : S.Opens) from trivial)
      (⊤ : S.Opens).2
  exact ⟨⟨U, hU, hsU⟩⟩

/-- Any two affine open neighbourhoods of `s` contain a common affine open neighbourhood of `s`. -/
instance : IsDirected (AffineNhds S s) (· ≤ ·) := by
  refine ⟨fun U V => ?_⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWUV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (show s ∈ U.opens ⊓ V.opens from ⟨U.2.2, V.2.2⟩) (U.opens ⊓ V.opens).2
  exact ⟨⟨W, hW, hsW⟩, hWUV.trans inf_le_left, hWUV.trans inf_le_right⟩

/-- An affine open neighbourhood of `s` is an open neighbourhood of `s`. -/
def inclusion : AffineNhds S s ⥤ (OpenNhds s)ᵒᵖ where
  obj U := op ⟨U.opens, U.2.2⟩
  map {U V} f := (homOfLE (show V.opens ≤ U.opens from leOfHom f)).op
  map_id _ := by apply Subsingleton.elim
  map_comp _ _ := by apply Subsingleton.elim

/-- The affine open neighbourhoods of `s` are cofinal among all its open neighbourhoods,
the affine opens being a basis of the topology. -/
theorem inclusion_final : (inclusion S s).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun V => ?_)
    fun {_ U} _ _ => ⟨U, 𝟙 U, Subsingleton.elim _ _⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, hUV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open V.unop.2 V.unop.1.2
  exact ⟨⟨U, hU, hsU⟩, ⟨(homOfLE hUV).op⟩⟩

/-- The inverse system of affine open neighbourhoods of `s`, as schemes. -/
noncomputable def diagram : (AffineNhds S s)ᵒᵖ ⥤ Scheme.{u} where
  obj i := i.unop.opens.toScheme
  map {i j} f := S.homOfLE (show i.unop.opens ≤ j.unop.opens from leOfHom f.unop)
  map_id _ := by simp
  map_comp _ _ := by simp

end AffineNhds

/-- The cone over the affine open neighbourhoods of `s` with vertex `Spec(𝒪_{S, s})`, whose
leg at `U` is the canonical morphism `Spec(𝒪_{S, s}) ⟶ U`. -/
noncomputable def affineNhdsSpecStalkCone : Cone (AffineNhds.diagram S s) where
  pt := Spec (S.presheaf.stalk s)
  π :=
    { app i := i.unop.opens.fromSpecStalkOfMem s i.unop.2.2
      naturality := by
        intro i j f
        apply (cancel_mono j.unop.opens.ι).mp
        simp [AffineNhds.diagram, Scheme.homOfLE_ι, Category.assoc] }

/-- The inverse system of affine open neighbourhoods of `s` is, stage by stage, the spectrum
of the ring of sections, by `AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
noncomputable def affineNhdsSpecDiagramIso :
    AffineNhds.diagram S s ≅
      (AffineNhds.inclusion S s ⋙ (OpenNhds.inclusion s).op ⋙ S.presheaf).op ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun i => i.unop.2.1.isoSpec) fun {i j} f =>
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _
      (show i.unop.opens ≤ j.unop.opens from leOfHom f.unop)).symm

/-- **The limit identity used in Stacks 0B80.** `Spec(𝒪_{S, s})` is the cofiltered limit of
the affine open neighbourhoods of `s`.

Dually `𝒪_{S, s} = colim 𝒪_S(U)` over the open neighbourhoods of `s`, and the affine ones are
cofinal among them; `Scheme.Spec` turns that colimit of rings into the limit of schemes. -/
@[ega "IV 8.1.2"]
noncomputable def isLimitAffineNhdsSpecStalkCone : IsLimit (affineNhdsSpecStalkCone S s) := by
  letI : (AffineNhds.inclusion S s).Final := AffineNhds.inclusion_final S s
  have hc : IsColimit (((colimit.cocone ((OpenNhds.inclusion s).op ⋙ S.presheaf))).whisker
      (AffineNhds.inclusion S s)) :=
    (Functor.Final.isColimitWhiskerEquiv (AffineNhds.inclusion S s) _).symm
      (colimit.isColimit ((OpenNhds.inclusion s).op ⋙ S.presheaf))
  apply (IsLimit.postcomposeHomEquiv (affineNhdsSpecDiagramIso S s) _).toFun
  apply IsLimit.ofIsoLimit (isLimitOfPreserves Scheme.Spec hc.op)
  refine Cone.ext (Iso.refl _) ?_
  intro i
  change Spec.map (S.presheaf.germ i.unop.opens s i.unop.2.2) =
    𝟙 _ ≫ i.unop.opens.fromSpecStalkOfMem s i.unop.2.2 ≫ i.unop.2.1.isoSpec.hom
  simpa only [Category.id_comp, IsAffineOpen.isoSpec_hom] using
    (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ i.unop.opens s i.unop.2.2).symm

end Scheme

namespace Space

/-! ### The same limit inside the big fppf site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)

/-- An affine open neighbourhood of `s`, as an object of the big fppf site of `S`. -/
noncomputable def affineNhdsSiteObject (U : Scheme.AffineNhds S s) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk U.opens.ι :
    B.obj (Scheme.size_lt_of_isOpenImmersion U.opens.ι hS) ⟶ B.obj hS)

/-- The inverse system of affine open neighbourhoods of `s`, as objects of the big fppf site
of `S`. -/
noncomputable def affineNhdsSiteSystem :
    (Scheme.AffineNhds S s)ᵒᵖ ⥤ BigFppfOver B S hS where
  obj i := affineNhdsSiteObject B S hS s i.unop
  map {i j} f := Over.homMk (ObjectProperty.homMk ((Scheme.AffineNhds.diagram S s).map f))
    (by
      apply ObjectProperty.hom_ext
      change S.homOfLE (show i.unop.opens ≤ j.unop.opens from leOfHom f.unop) ≫
        j.unop.opens.ι = i.unop.opens.ι
      simp)
  map_id i := by
    ext
    exact (Scheme.AffineNhds.diagram S s).map_id i
  map_comp f g := by
    ext
    exact (Scheme.AffineNhds.diagram S s).map_comp f g

/-- The scheme morphism underlying a transition morphism of the inverse system of affine open
neighbourhoods of `s` in the big fppf site is the inclusion of one open into the other. -/
@[simp]
theorem affineNhdsSiteSystem_map_left_hom {i j : (Scheme.AffineNhds S s)ᵒᵖ} (f : i ⟶ j) :
    (((affineNhdsSiteSystem B S hS s).map f).left).hom =
      S.homOfLE (show i.unop.opens ≤ j.unop.opens from leOfHom f.unop) :=
  rfl

variable {B S hS s}

/-- The cone in the big fppf site of `S` over the affine open neighbourhoods of `s`, with
vertex an object `T` of the site identified with `Spec(𝒪_{S, s})` over `S`. -/
noncomputable def affineNhdsSiteConeOfStalkIso (T : BigFppfOver B S hS)
    (e : T.left.1 ≅ Spec (S.presheaf.stalk s))
    (he : B.inclusion.map T.hom = e.hom ≫ S.fromSpecStalk s) :
    Cone (affineNhdsSiteSystem B S hS s) where
  pt := T
  π :=
    { app i := Over.homMk
        (ObjectProperty.homMk (e.hom ≫ i.unop.opens.fromSpecStalkOfMem s i.unop.2.2))
        (by
          apply ObjectProperty.hom_ext
          change (e.hom ≫ i.unop.opens.fromSpecStalkOfMem s i.unop.2.2) ≫ i.unop.opens.ι =
            B.inclusion.map T.hom
          simpa only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι] using he.symm)
      naturality := by
        intro i j f
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        apply (cancel_mono j.unop.opens.ι).mp
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Over.comp_left,
          Over.homMk_left, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
          ObjectProperty.homMk_hom, affineNhdsSiteSystem_map_left_hom]
        change (e.hom ≫ j.unop.opens.fromSpecStalkOfMem s j.unop.2.2) ≫ j.unop.opens.ι =
          ((e.hom ≫ i.unop.opens.fromSpecStalkOfMem s i.unop.2.2) ≫
            S.homOfLE (show i.unop.opens ≤ j.unop.opens from leOfHom f.unop)) ≫ j.unop.opens.ι
        simp [Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι] }

/-- **The limit identity of Stacks 0B80, inside the big fppf site.** An object of the site
identified with `Spec(𝒪_{S, s})` over `S` is the limit of the affine open neighbourhoods of
`s`, taken in the site.

The forgetful functors from the site to schemes reflect limits over a connected index
category, so this is `AlgebraicGeometry.Scheme.isLimitAffineNhdsSpecStalkCone`. -/
noncomputable def isLimitAffineNhdsSiteConeOfStalkIso (T : BigFppfOver B S hS)
    (e : T.left.1 ≅ Spec (S.presheaf.stalk s))
    (he : B.inclusion.map T.hom = e.hom ≫ S.fromSpecStalk s) :
    IsLimit (affineNhdsSiteConeOfStalkIso T e he) := by
  letI : IsConnected (Scheme.AffineNhds S s)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget (B.obj hS))
  apply isLimitOfReflects B.inclusion
  exact IsLimit.ofIsoLimit (Scheme.isLimitAffineNhdsSpecStalkCone S s)
    (Cone.ext e.symm (by
      intro i
      simp only [affineNhdsSiteConeOfStalkIso, Scheme.affineNhdsSpecStalkCone,
        Functor.mapCone_π_app, Over.forget_map, Over.homMk_left, ObjectProperty.ι_map,
        ObjectProperty.homMk_hom, Iso.symm_hom]
      exact (Iso.inv_hom_id_assoc e _).symm))

/-! ### Base change along a morphism to the terminal presheaf -/

section BaseChange

variable (B S hS)

/-- The structure morphism of an object of the big fppf site of `S`, as a morphism of
presheaves to the presheaf represented by the terminal object of the site. -/
def yonedaStructure :
    yoneda (C := BigFppfOver B S hS) ⟶
      (Functor.const _).obj (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) where
  app T := yoneda.map (Over.homMk T.hom (by simp))
  naturality {T U} g := by
    simp only [Functor.const_obj_map, ← yoneda.map_comp]
    congr 1
    exact Over.OverMorphism.ext g.w

variable {B S hS}

/-- Base change of a presheaf `X` over `S` along the objects of the site: the functor sending
an object `U` of the big fppf site of `S` to the fibre product `X ×_S U`. -/
noncomputable def baseChangeSiteFunctor
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :
    BigFppfOver B S hS ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.lift yoneda (yonedaStructure B S hS) ⋙ Over.pullback f ⋙ Over.forget X

/-- **The base change step of Stacks 0B80.** Base change along `f : X ⟶ *` carries a limiting
cone of objects of the big fppf site over a connected index category to a limiting cone of
presheaves: `X ×_S lim U = lim (X ×_S U)`.

This is *not* an instance of Stacks 07SF part (2)
(`AlgebraicGeometry.Space.isLimitPullbackLimitOverPost`), which base changes a limit of
presheaves along a morphism to one of its *stages*; here the system is base changed along a
fixed morphism to the terminal presheaf. What makes it work is the same mechanism: base change
is a right adjoint followed by a functor creating connected limits. -/
noncomputable def isLimitBaseChangeMapCone
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    {I : Type v} [Category.{v} I] [IsConnected I] {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hc : IsLimit c) : IsLimit ((baseChangeSiteFunctor f).mapCone c) := by
  change IsLimit ((Over.pullback f ⋙ Over.forget X).mapCone
    ((Over.lift yoneda (yonedaStructure B S hS)).mapCone c))
  exact isLimitOfPreserves (Over.pullback f ⋙ Over.forget X)
    (isLimitOfReflects (Over.forget _) (isLimitOfPreserves yoneda hc))

/-- **`X ×_S Spec(𝒪_{S, s}) = lim_U X ×_S U`**, the identity the proof of Stacks 0B80 rests
on: the base change of `X` to the local ring of `S` at `s` is the limit of its base changes to
the affine open neighbourhoods of `s`. -/
noncomputable def isLimitBaseChangeAffineNhdsCone
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (T : BigFppfOver B S hS) (e : T.left.1 ≅ Spec (S.presheaf.stalk s))
    (he : B.inclusion.map T.hom = e.hom ≫ S.fromSpecStalk s) :
    IsLimit ((baseChangeSiteFunctor f).mapCone (affineNhdsSiteConeOfStalkIso T e he)) :=
  letI : IsConnected (Scheme.AffineNhds S s)ᵒᵖ := IsCofiltered.isConnected _
  isLimitBaseChangeMapCone f (isLimitAffineNhdsSiteConeOfStalkIso T e he)

end BaseChange

end Space

end AlgebraicGeometry

end
