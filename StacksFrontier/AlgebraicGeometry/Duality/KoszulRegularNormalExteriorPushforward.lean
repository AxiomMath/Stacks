module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExteriorAlgebraContinuous
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalExterior
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulRegularDerivedDual
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportInternalHom
import all StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence

/-!
# The exterior algebra of the normal sheaf, pushed forward along a closed immersion

Let `i : X ⟶ Y` be a closed immersion of schemes with defining ideal sheaf `𝓘 ⊆ 𝒪_Y`, and let
`𝒩 = 𝓗om_{𝒪_X}(𝒞_{X/Y}, 𝒪_X)` be its normal sheaf. The normal sheaf of the ideal sheaf `𝓘` in
the sense of [Stacks, Tag 0BQW], `𝓗om_{𝒪_Y}(𝓘/𝓘², 𝒪_Y/𝓘)`, is a sheaf of `𝒪_Y/𝓘`-modules, and
[Stacks, Tag 0BQZ] is phrased with the exterior powers of it over `𝒪_Y/𝓘`; [Stacks, Tag 0BR0] is
phrased with the exterior powers `⋀ⁿ𝒩` over `𝒪_X`. This file identifies the two: there is an
exterior algebra over `𝒪_Y/𝓘` of the former whose pieces, read over `𝒪_Y`, are the `i_* ⋀ⁿ𝒩`.

The proof has three steps.

1. `𝒪_Y/𝓘 ≅ i_* 𝒪_X` as sheaves of rings, compatibly with the two maps out of `𝒪_Y`: the
   comorphism is surjective with kernel `𝓘` (`Stacks.Sites.quotientRingSheafIso`).
2. The pushforward of an exterior algebra along a closed embedding is an exterior algebra of the
   pushforward. This is `SheafOfModules.ContinuousPushforward.isExteriorAlgebra_pushforward`,
   which asks of the continuous functor `Opens.map i` only that pushforward commute with
   sheafification. That functor is not cocontinuous, but along a closed embedding pushforward
   still commutes with sheafification, every module over the structure sheaf having a single
   section over the empty open.
3. `𝓗om_{𝒪_Y}(𝓘/𝓘², 𝒪_Y/𝓘) ≅ i_* 𝒩` as `𝒪_Y`-modules: `𝓘/𝓘² ≅ i_* i^* 𝓘 = i_* 𝒞_{X/Y}`
   because `𝓘/𝓘²` is annihilated by `𝓘` and `i^*` kills `𝓘² ⟶ 𝓘`, and then the underived form of
   [Stacks, Tag 0E2I] computes `𝓗om_{𝒪_Y}(i_* 𝒞_{X/Y}, i_* 𝒪_X)`.

## Main definitions

* `Stacks.Duality.KoszulRegular.quotientRingSheafRingIso`: `𝒪_Y/𝓘 ≅ i_* 𝒪_X`.
* `Stacks.Duality.KoszulRegular.idealQuotientBySquareIsoPushforward`: `𝓘/𝓘² ≅ i_* i^* 𝓘`.
* `Stacks.Duality.KoszulRegular.normalSheafOfIdealSheafIsoPushforward`: the normal sheaf of `𝓘`
  is `i_* 𝒩`.
* `SheafOfModules.restrictScalarsCompIso`: restriction of scalars along a composite.

## Main results

* `Stacks.Duality.KoszulRegular.exists_exteriorAlgebra_pushforward_iso`: an exterior algebra
  over `𝒪_Y/𝓘` of the normal sheaf of `𝓘` whose pieces, read over `𝒪_Y`, are the `i_* ⋀ⁿ𝒩`.
* `isIso_pushforwardSheafifyHom_of_isClosedEmbedding`, in
  `Stacks.SheafOfModules.PushforwardSheafification`: sheafification of presheaves of modules
  commutes with pushforward along a closed embedding.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.scalarRestrict_of_iso`: an exterior algebra
  restricted along an isomorphism of sheaves of rings is an exterior algebra.
* `Stacks.Duality.idealSquareInclusion_comp_eq_zero` and
  `Stacks.Duality.smul_idealQuotientBySquare_eq_zero`: a morphism out of `𝓘` into a module
  annihilated by `𝓘` kills `𝓘²`, and `𝓘` annihilates `𝓘/𝓘²`.

## References

* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 0BQW](https://stacks.math.columbia.edu/tag/0BQW)
* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
  PresheafOfModules Stacks.SheafOfModules.PushforwardSheafification

universe w t v u v' u'

open AlgebraicGeometry

namespace CategoryTheory.Presheaf

section ClosedEmbedding

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
  {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  {F F' : (Opens X)ᵒᵖ ⥤ A} (φ : F ⟶ F')

include hf in
/-- Along a closed embedding `f`, every open neighbourhood of a point of the range in an open
`U` of the target contains the image-side open of a given open of the source: the open `W` of
`X` lying in `f⁻¹ U` is `f⁻¹ V` for an open `V ≤ U` of `Y`. -/
theorem _root_.TopologicalSpace.Opens.exists_map_obj_eq_of_isClosedEmbedding (U : Opens Y)
    (W : Opens X) (hW : W ≤ (Opens.map f).obj U) :
    ∃ V : Opens Y, V ≤ U ∧ (Opens.map f).obj V = W := by
  obtain ⟨W', hW'o, hW'⟩ := hf.isInducing.isOpen_iff.1 W.isOpen
  refine ⟨⟨W', hW'o⟩ ⊓ U, inf_le_right, ?_⟩
  ext x
  change x ∈ f ⁻¹' W' ∧ f x ∈ U ↔ x ∈ W
  rw [hW']
  exact ⟨fun h => h.1, fun h => ⟨h, hW h⟩⟩

include hf in
/-- The open complement of the closed range of a closed embedding, cut down to `U`, has empty
inverse image. -/
theorem _root_.TopologicalSpace.Opens.map_obj_inf_compl_range_eq_bot (U : Opens Y) :
    (Opens.map f).obj (⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩ ⊓ U) = ⊥ := by
  ext x
  simp

/-- A sieve covering `f⁻¹ U` contains, around a point of `f⁻¹ U`, the pullback of an open
`V ≤ U` of `Y` containing the image of that point. -/
private theorem exists_map_mem_sieve_of_isClosedEmbedding (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding f) (U : Opens Y)
    (S : Sieve ((Opens.map f).obj U))
    (hS : S ∈ Opens.grothendieckTopology X ((Opens.map f).obj U)) (x : X) (hx : f x ∈ U) :
    ∃ V : Opens Y, ∃ h : V ⟶ U, S ((Opens.map f).map h) ∧ f x ∈ V := by
  obtain ⟨W, g, hg, hxW⟩ := (Opens.mem_grothendieckTopology _).1 hS x hx
  obtain ⟨V, hVU, hVW⟩ :=
    TopologicalSpace.Opens.exists_map_obj_eq_of_isClosedEmbedding f hf U W (leOfHom g)
  refine ⟨V, homOfLE hVU, ?_, show x ∈ (Opens.map f).obj V from hVW ▸ hxW⟩
  have h := S.downward_closed hg (eqToHom hVW)
  rwa [Subsingleton.elim (eqToHom hVW ≫ g) ((Opens.map f).map (homOfLE hVU))] at h

include hf in
/-- **Pulling a locally surjective morphism of presheaves back along a closed embedding.**
Restriction along `Opens.map f` is not cocontinuous for a closed embedding `f` — the empty
covering of the empty open of `X` comes from no covering of a nonempty open disjoint from the
range — so `Presheaf.isLocallySurjective_whisker` does not apply. Off the range one needs
instead that the morphism is surjective over the empty open, which holds for every morphism into
a sheaf of abelian groups. -/
theorem isLocallySurjective_whiskerLeft_opensMap_of_isClosedEmbedding
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ]
    (hbot : ∀ W : Opens X, W = ⊥ → ∀ s : ToType (F'.obj (op W)), ∃ t, φ.app (op W) t = s) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerLeft (Opens.map f).op φ) := by
  constructor
  intro U s
  rw [Opens.mem_grothendieckTopology]
  intro y hy
  by_cases hyr : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hyr
    exact exists_map_mem_sieve_of_isClosedEmbedding f hf U _
      (Presheaf.imageSieve_mem (Opens.grothendieckTopology X) φ s) x hy
  · refine ⟨⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩ ⊓ U, homOfLE inf_le_right, ?_,
      ⟨hyr, hy⟩⟩
    exact hbot _ (TopologicalSpace.Opens.map_obj_inf_compl_range_eq_bot f hf U) _

include hf in
/-- **Pulling a locally injective morphism of presheaves back along a closed embedding.** As for
`isLocallySurjective_whiskerLeft_opensMap_of_isClosedEmbedding`, off the range one needs instead
that the source has at most one section over the empty open, which holds for every presheaf of
modules over a sheaf of rings. -/
theorem isLocallyInjective_whiskerLeft_opensMap_of_isClosedEmbedding
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ]
    (hbot : ∀ W : Opens X, W = ⊥ → ∀ s t : ToType (F.obj (op W)), s = t) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (Functor.whiskerLeft (Opens.map f).op φ) := by
  constructor
  intro U s t hst
  rw [Opens.mem_grothendieckTopology]
  intro y hy
  by_cases hyr : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hyr
    exact exists_map_mem_sieve_of_isClosedEmbedding f hf U.unop _
      (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) φ s t hst) x hy
  · refine ⟨⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩ ⊓ U.unop, homOfLE inf_le_right, ?_,
      ⟨hyr, hy⟩⟩
    exact hbot _ (TopologicalSpace.Opens.map_obj_inf_compl_range_eq_bot f hf U.unop) _ _

include hf in
/-- `isLocallySurjective_whiskerLeft_opensMap_of_isClosedEmbedding` for a morphism into a sheaf
of abelian groups, which has a single section over the empty open. -/
theorem isLocallySurjective_whiskerLeft_opensMap_of_isSheaf
    {F F' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F ⟶ F')
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ]
    (hF' : Presheaf.IsSheaf (Opens.grothendieckTopology X) F') :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerLeft (Opens.map f).op φ) := by
  refine isLocallySurjective_whiskerLeft_opensMap_of_isClosedEmbedding f hf φ ?_
  rintro W rfl s
  refine ⟨0, ?_⟩
  exact (AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEmpty (⟨F', hF'⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)).isZero).elim _ _

end ClosedEmbedding

end CategoryTheory.Presheaf

namespace Stacks.SheafOfModules.PushforwardSheafification


section ClosedEmbeddingSheafify

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
  (Osharp : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

include hf in
/-- The pushed-forward sheafification unit along a closed embedding is locally injective. -/
theorem isLocallyInjective_pushforwardToSheafify_of_isClosedEmbedding
    (P : PresheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp).obj) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (pushforwardToSheafify.{u} (Opens.grothendieckTopology Y) (Opens.map f)
        (toRingCat (Opens.grothendieckTopology X) Osharp) P) := by
  rw [pushforwardToSheafify_eq]
  refine Presheaf.isLocallyInjective_whiskerLeft_opensMap_of_isClosedEmbedding f hf _ ?_
  rintro W rfl s t
  have : Subsingleton (Osharp.obj.obj (op ⊥)) :=
    CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Osharp)
  have : Subsingleton ((toRingCat (Opens.grothendieckTopology X) Osharp).obj.obj (op ⊥)) :=
    ‹Subsingleton (Osharp.obj.obj (op ⊥))›
  have : Subsingleton (P.obj (op ⊥)) :=
    Module.subsingleton ((toRingCat (Opens.grothendieckTopology X) Osharp).obj.obj (op ⊥)) _
  exact Subsingleton.elim (α := P.obj (op ⊥)) s t

include hf in
/-- The pushed-forward sheafification unit along a closed embedding is locally surjective. -/
theorem isLocallySurjective_pushforwardToSheafify_of_isClosedEmbedding
    (P : PresheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp).obj) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (pushforwardToSheafify.{u} (Opens.grothendieckTopology Y) (Opens.map f)
        (toRingCat (Opens.grothendieckTopology X) Osharp) P) := by
  rw [pushforwardToSheafify_eq]
  exact Presheaf.isLocallySurjective_whiskerLeft_opensMap_of_isSheaf f hf _
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P.presheaf).property

include hf in
/-- **Sheafification of presheaves of modules commutes with pushforward along a closed
embedding.** This is `Stacks.SheafOfModules.PushforwardSheafification.isIso_pushforwardSheafifyHom`
for the functor `Opens.map f`, which is not cocontinuous; what replaces cocontinuity is that the
structure sheaf, hence every module over it, has a single section over the empty open. -/
theorem isIso_pushforwardSheafifyHom_of_isClosedEmbedding
    (P : PresheafOfModules.{u} (toRingCat (Opens.grothendieckTopology X) Osharp).obj) :
    IsIso (pushforwardSheafifyHom.{u} (Opens.grothendieckTopology Y) (Opens.map f)
      (toRingCat (Opens.grothendieckTopology X) Osharp) P) :=
  isIso_pushforwardSheafifyHom_of_isLocallyBijective _ _ _ P
    (isLocallyInjective_pushforwardToSheafify_of_isClosedEmbedding f hf Osharp P)
    (isLocallySurjective_pushforwardToSheafify_of_isClosedEmbedding f hf Osharp P)

end ClosedEmbeddingSheafify

end Stacks.SheafOfModules.PushforwardSheafification

namespace SheafOfModules

section ScalarRestrictIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Restriction of scalars along `f` of the restriction along `g` is the restriction along any
`h` with `f ≫ g = h`, by the identity on local sections. -/
def restrictScalarsCompIso {R₁ R₂ R₃ : Sheaf J RingCat.{t}} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃)
    (h : R₁ ⟶ R₃) (hfg : f ≫ g = h) (M : SheafOfModules.{w} R₃) :
    (restrictScalars f).obj ((restrictScalars g).obj M) ≅ (restrictScalars h).obj M where
  hom := ⟨{ app X := (ModuleCat.restrictScalarsComp'App (f.hom.app X).hom (g.hom.app X).hom
              (h.hom.app X).hom (by rw [← hfg]; rfl) (M.val.obj X)).inv
            naturality := fun _ => by ext; rfl }⟩
  inv := ⟨{ app X := (ModuleCat.restrictScalarsComp'App (f.hom.app X).hom (g.hom.app X).hom
              (h.hom.app X).hom (by rw [← hfg]; rfl) (M.val.obj X)).hom
            naturality := fun _ => by ext; rfl }⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- Restriction of scalars along `f` and then along `g` is the identity on sheaves of modules
when `f ≫ g = 𝟙`, by the identity on local sections. -/
def restrictScalarsCompIsoOfCompEqId {R S : Sheaf J RingCat.{t}} (f : R ⟶ S) (g : S ⟶ R)
    (hfg : f ≫ g = 𝟙 R) (M : SheafOfModules.{w} R) :
    (restrictScalars f).obj ((restrictScalars g).obj M) ≅ M where
  hom := ⟨{ app X := (ModuleCat.restrictScalarsComp'App (f.hom.app X).hom (g.hom.app X).hom
              (RingHom.id _) (congrArg (fun φ : R ⟶ R => (φ.hom.app X).hom) hfg).symm
              (M.val.obj X)).inv ≫
              (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj X)).hom
            naturality := fun _ => by ext; rfl }⟩
  inv := ⟨{ app X := (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj X)).inv ≫
              (ModuleCat.restrictScalarsComp'App (f.hom.app X).hom (g.hom.app X).hom
              (RingHom.id _) (congrArg (fun φ : R ⟶ R => (φ.hom.app X).hom) hfg).symm
              (M.val.obj X)).hom
            naturality := fun _ => by ext; rfl }⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

open _root_.SheafOfModules.GradedAlgebra in
/-- **The universal property of an exterior algebra crosses an isomorphism of sheaves of rings**,
in the direction which `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_scalarRestrict` does
not cover: restriction of scalars along an isomorphism `θ` carries an exterior algebra to an
exterior algebra. It is `of_scalarRestrict` along `θ⁻¹`, once the twice-restricted algebra is
identified with the original by the identity on local sections. -/
theorem GradedAlgebra.IsExteriorAlgebra.scalarRestrict_of_iso {R S : Sheaf J RingCat.{t}}
    (θ : S ≅ R)
    {B : GradedAlgebra.{t, w} R} {M : SheafOfModules.{w} R} {gen : M ⟶ B.piece 1}
    (hB : IsExteriorAlgebra B gen) :
    IsExteriorAlgebra (GradedAlgebra.scalarRestrict θ.hom B) (genScalarRestrict θ.hom gen) := by
  let U : UnitalHom B (GradedAlgebra.scalarRestrict θ.inv (GradedAlgebra.scalarRestrict θ.hom B)) :=
    { app n := (restrictScalarsCompIsoOfCompEqId θ.inv θ.hom θ.inv_hom_id (B.piece n)).inv
      map_mul _ _ _ _ _ := rfl
      map_one _ := rfl }
  have : ∀ n, IsIso (U.app n) := fun n => Iso.isIso_inv _
  have h1 := IsUniversal.ofDegreewiseIso hB U
    ((squareZero_scalarRestrict_iff θ.inv _).2 ((squareZero_scalarRestrict_iff θ.hom _).2 hB.1) :
      SquareZero (genScalarRestrict θ.inv (genScalarRestrict θ.hom gen)))
  have h2 : IsExteriorAlgebra _ _ := IsExteriorAlgebra.comp_iso h1
    (restrictScalarsCompIsoOfCompEqId θ.inv θ.hom θ.inv_hom_id M).hom inferInstance
  have : Presheaf.IsLocallySurjective J θ.inv.hom := inferInstance
  refine IsExteriorAlgebra.of_scalarRestrict θ.inv ?_
  convert h2 using 1
  ext
  rfl

end ScalarRestrictIso

end SheafOfModules


namespace Stacks.Duality

section IdealSquare

variable (Y : RingedSpace.{u, u})
  (I : (_root_.SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
      Y.sheaf)).Submodule)

variable {Y I} in
/-- The local sections of `ℐ` over `U` on which a morphism out of `ℐ` vanishes, as an ideal of
the sections of the structure sheaf over `U`. -/
def idealKernelObj {T : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
    (f : I.toSheafOfModules ⟶ T) (U : (Opens Y.carrier)ᵒᵖ) :
    Submodule
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf).obj.obj U)
      ((_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
          Y.sheaf)).val.obj U) where
  carrier := {s | ∃ h : s ∈ I.obj U, f.val.app U ⟨s, h⟩ = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(I.obj U).add_mem ha hb, ?_⟩
    have h := (f.val.app U).hom.map_add ⟨a, ha⟩ ⟨b, hb⟩
    rwa [ha', hb', add_zero] at h
  zero_mem' := ⟨(I.obj U).zero_mem, (f.val.app U).hom.map_zero⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨(I.obj U).smul_mem c ha, ?_⟩
    have h := (f.val.app U).hom.map_smul c ⟨a, ha⟩
    rwa [ha', smul_zero] at h

variable {Y I} in
/-- Membership in `Stacks.Duality.idealKernelObj`. -/
theorem mem_idealKernelObj {T : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
    (f : I.toSheafOfModules ⟶ T) {U : (Opens Y.carrier)ᵒᵖ}
    (s : (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf)).val.obj U) :
    s ∈ idealKernelObj f U ↔ ∃ h : s ∈ I.obj U, f.val.app U ⟨s, h⟩ = 0 :=
  Iff.rfl

variable {Y I} in
/-- The sheaf of ideals of the local sections of `ℐ` on which a morphism out of `ℐ` vanishes. -/
def idealKernel {T : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
    (f : I.toSheafOfModules ⟶ T) :
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf)).Submodule where
  obj := idealKernelObj f
  map {U V} g s hs := by
    obtain ⟨hs, hs'⟩ := (mem_idealKernelObj f s).1 hs
    refine (mem_idealKernelObj f _).2 ⟨I.toSubmodule.map g hs, ?_⟩
    have h := PresheafOfModules.naturality_apply f.val g ⟨s, hs⟩
    rwa [hs', map_zero] at h
  isSheaf U s hs := by
    have hsI : s ∈ I.obj U := by
      refine I.isSheaf s (GrothendieckTopology.superset_covering _ ?_ hs)
      exact fun V g hg => ((mem_idealKernelObj f _).1 hg).1
    have hT' : Presieve.IsSheaf (Opens.grothendieckTopology Y.carrier)
        (T.val.presheaf ⋙ forget AddCommGrpCat.{u}) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ T.isSheaf)
    refine (mem_idealKernelObj f s).2 ⟨hsI, (hT' _ hs).isSeparatedFor.ext fun V g hg => ?_⟩
    change T.val.map g.op (f.val.app U ⟨s, hsI⟩) = T.val.map g.op 0
    refine ((PresheafOfModules.naturality_apply f.val g.op ⟨s, hsI⟩).symm.trans ?_).trans
      (map_zero _).symm
    exact ((mem_idealKernelObj f _).1 hg).2

/-- **A morphism out of a sheaf of ideals into a module it annihilates kills the square of the
ideal.** The local sections of `ℐ` on which the morphism vanishes form a sheaf of ideals
containing every product of two local sections of `ℐ`, because `f(ab) = a f(b) = 0`; so it
contains `ℐ²`. -/
theorem idealSquareInclusion_comp_eq_zero
    {T : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)}
    (hT : ∀ (U : (Opens Y.carrier)ᵒᵖ)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf).obj.obj U),
      a ∈ I.obj U → ∀ t : T.val.obj U, a • t = 0)
    (f : I.toSheafOfModules ⟶ T) (U : (Opens Y.carrier)ᵒᵖ)
    (c : (idealSquare Y I).toSheafOfModules.val.obj U) :
    f.val.app U ((idealSquareInclusion Y I).val.app U c) = 0 := by
  have hle : idealSquare Y I ≤ idealKernel f :=
    sInf_le fun U a b ha hb => (mem_idealKernelObj f (a * b)).2 ⟨(I.obj U).smul_mem a hb, by
      have h := (f.val.app U).hom.map_smul a ⟨b, hb⟩
      rwa [hT U a ha] at h⟩
  exact ((mem_idealKernelObj f _).1 (_root_.SheafOfModules.Submodule.le_iff.mp hle U c.2)).2

/-- A product of two local sections of a sheaf of ideals is a local section of its square. -/
theorem mul_mem_idealSquare {U : (Opens Y.carrier)ᵒᵖ}
    {a b : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
      Y.sheaf).obj.obj U}
    (ha : a ∈ I.obj U) (hb : b ∈ I.obj U) :
    (show (_root_.SheafOfModules.unit (structureSheafRing Y)).val.obj U from a * b) ∈
      (idealSquare Y I).obj U := by
  refine (Submodule.mem_iInf _).2 fun N => (Submodule.mem_iInf _).2 fun hN => ?_
  obtain ⟨N', hN', rfl⟩ := hN
  exact hN' U a b ha hb

/-- **A sheaf of ideals annihilates its conormal quotient `ℐ/ℐ²`.** A local section of `ℐ/ℐ²` is
locally the class of a section `t` of `ℐ`, the quotient map being an epimorphism of sheaves; a
section `a` of `ℐ` then acts on it by the class of `at`, which lies in `ℐ²`. -/
theorem smul_idealQuotientBySquare_eq_zero (U : (Opens Y.carrier)ᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
      Y.sheaf).obj.obj U)
    (ha : a ∈ I.obj U) (m : (idealQuotientBySquare Y I).val.obj U) : a • m = 0 := by
  have : Epi (cokernel.π (idealSquareInclusion Y I)) := coequalizer.π_epi
  have hπ := @Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _ _ _ _ _ _ _
    (cokernel.π (idealSquareInclusion Y I)) this
  refine (Stacks.SheafOfModules.isSheaf_forgetPresheaf (idealQuotientBySquare Y I) _
    (hπ.imageSieve_mem (U := U.unop) m)).isSeparatedFor.ext fun V g hg => ?_
  obtain ⟨t, ht⟩ := hg
  change (idealQuotientBySquare Y I).val.map g.op (a • m) =
    (idealQuotientBySquare Y I).val.map g.op 0
  rw [map_zero, PresheafOfModules.map_smul]
  have ht' : (cokernel.π (idealSquareInclusion Y I)).val.app (op V) t =
      (idealQuotientBySquare Y I).val.map g.op m := ht
  rw [← ht']
  refine (((cokernel.π (idealSquareInclusion Y I)).val.app (op V)).hom.map_smul _ t).symm.trans ?_
  have hz := congrArg (fun φ => φ.val.app (op V)
    (⟨_, mul_mem_idealSquare Y I (I.toSubmodule.map g.op ha) t.2⟩ :
      (idealSquare Y I).toSheafOfModules.val.obj (op V)))
    (cokernel.condition (idealSquareInclusion Y I))
  exact hz

end IdealSquare

end Stacks.Duality

namespace Stacks.Duality.KoszulRegular

open Stacks.AlgebraicGeometry.RegularIdealSheaf RingedSpaceModuleAdjunction

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- The comorphism `𝒪_Y ⟶ i_* 𝒪_X` of a closed immersion, as a morphism of sheaves of commutative
rings on `Y`. -/
def structureSheafPushforwardHom :
    Y.sheaf ⟶ ((Opens.map i.base).sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.sheaf :=
  ⟨i.c⟩

/-- The comorphism of a closed immersion is locally surjective. -/
instance isLocallySurjective_structureSheafPushforwardHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (structureSheafPushforwardHom i).hom :=
  Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i

omit [IsClosedImmersion i] in
/-- The kernel of the comorphism over an open is the ideal of sections of the defining ideal
sheaf there, which is how that ideal sheaf is defined. -/
theorem ker_structureSheafPushforwardHom_app (V : (Opens Y)ᵒᵖ) :
    RingHom.ker ((structureSheafPushforwardHom i).hom.app V).hom =
      Stacks.Sites.sectionIdeal (O := Y.sheaf) (definingIdealOfHom i) V := by
  ext s
  exact Iff.rfl

/-- **`𝒪_Y/𝓘 ≅ i_* 𝒪_X`** for the defining ideal sheaf `𝓘` of a closed immersion, as sheaves of
commutative rings on `Y`: the comorphism is surjective and its kernel is `𝓘`. -/
def quotientRingSheafIsoPushforward :
    Stacks.Sites.quotientRingSheaf.{u, u, u} (definingIdealOfHom i) ≅
      ((Opens.map i.base).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.sheaf :=
  Stacks.Sites.quotientRingSheafIso (structureSheafPushforwardHom i) (definingIdealOfHom i)
    (ker_structureSheafPushforwardHom_app i)

/-- `𝒪_Y/𝓘 ≅ i_* 𝒪_X` read as sheaves of rings: the target is the ring sheaf over which the
pushforward of sheaves of `𝒪_X`-modules along `Opens.map i.base` lives. -/
def quotientRingSheafRingIso :
    toRingCat (Opens.grothendieckTopology Y)
        (Stacks.Sites.quotientRingSheaf.{u, u, u} (definingIdealOfHom i)) ≅
      pushforwardRingSheaf (Opens.grothendieckTopology Y) (Opens.map i.base)
        (toRingCat (Opens.grothendieckTopology X) X.sheaf) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    (quotientRingSheafIsoPushforward i)

/-- The identification `𝒪_Y/𝓘 ≅ i_* 𝒪_X` carries the quotient map to the comorphism. -/
theorem quotientRingHom_comp_quotientRingSheafRingIso_hom :
    Stacks.Sites.quotientRingHom (definingIdealOfHom i) ≫ (quotientRingSheafRingIso i).hom =
      structureSheafHom (Stacks.Duality.closedQuotient i).i := by
  have h := Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafDesc
    (structureSheafPushforwardHom i) (definingIdealOfHom i)
    (fun V => (ker_structureSheafPushforwardHom_app i V).ge)
  rw [← Stacks.Sites.quotientRingSheafIso_hom (structureSheafPushforwardHom i)
    (definingIdealOfHom i) (ker_structureSheafPushforwardHom_app i)] at h
  exact (Functor.map_comp _ _ _).symm.trans <| congrArg
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).map h

local notation "𝓘" => definingIdealOfHom i

/-- A section of the defining ideal sheaf lies in the kernel ideal of the closed quotient
morphism. -/
theorem mem_kernelIdeal_of_mem_definingIdealOfHom {U : Opens Y}
    {a : (structureSheafRing Y.toRingedSpace).obj.obj (op U)} (ha : a ∈ (𝓘).obj (op U)) :
    a ∈ (Stacks.Duality.closedQuotient i).kernelIdeal U :=
  (SheafOfModules.unitToPushforwardObjUnit_val_app_apply _ _).symm.trans
    ((mem_definingIdealOfHom i U a).1 ha)

/-- **The defining ideal sheaf kills every direct image** along the closed immersion: a section
`a` of `𝓘` acts on `i_* M` through its image in `i_* 𝒪_X`, which is zero. -/
theorem smul_modulePushforward_eq_zero (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (U : Opens (Stacks.Duality.closedQuotient i).X)
    (a : (structureSheafRing (Stacks.Duality.closedQuotient i).X).obj.obj (op U))
    (ha : a ∈ (Stacks.Duality.closedQuotient i).kernelIdeal U)
    (m : ((modulePushforward (Stacks.Duality.closedQuotient i).i).obj M).val.obj (op U)) :
    a • m = 0 :=
  ((Stacks.Duality.closedQuotient i).modulePushforward_essImage_iff _).1
    ((modulePushforward (Stacks.Duality.closedQuotient i).i).obj_mem_essImage M) U a ha m

/-- The conormal quotient `𝓘/𝓘²` of the defining ideal sheaf is a direct image along `i`, so the
unit `𝓘/𝓘² ⟶ i_* i^* (𝓘/𝓘²)` is an isomorphism. -/
instance isIso_unit_idealQuotientBySquare :
    IsIso ((modulePullbackPushforwardAdjunction (Stacks.Duality.closedQuotient i).i).unit.app
      (Stacks.Duality.idealQuotientBySquare Y.toRingedSpace (𝓘))) := by
  have := (Stacks.Duality.closedQuotient i).full_modulePushforward
  have := (Stacks.Duality.closedQuotient i).faithful_modulePushforward
  refine (Adjunction.isIso_unit_app_iff_mem_essImage _).2
    (((Stacks.Duality.closedQuotient i).modulePushforward_essImage_iff _).2 ?_)
  intro U a ha m
  exact Stacks.Duality.smul_idealQuotientBySquare_eq_zero Y.toRingedSpace (𝓘) (op U) a
    ((mem_definingIdealOfHom i U a).2
      ((SheafOfModules.unitToPushforwardObjUnit_val_app_apply _ _).trans ha)) m

/-- **The unit `𝓘 ⟶ i_* i^* 𝓘` kills `𝓘²`**: it is a morphism into a direct image, which `𝓘`
annihilates. -/
theorem idealSquareInclusion_comp_unit :
    Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘) ≫
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (𝓘).toSheafOfModules = 0 := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun c => ?_))
  exact Stacks.Duality.idealSquareInclusion_comp_eq_zero Y.toRingedSpace (𝓘)
    (fun U a ha t => smul_modulePushforward_eq_zero i _ U.unop a
      (mem_kernelIdeal_of_mem_definingIdealOfHom i ha) t) _ U c

/-- The inverse of `i^*` of the projection `𝓘 ⟶ 𝓘/𝓘²`: the transpose of the unit of `𝓘`,
which factors through `𝓘/𝓘²` because it kills `𝓘²`. -/
def modulePullbackIdealQuotientBySquareInv :
    (modulePullback i.toLRSHom.toShHom).obj
        (Stacks.Duality.idealQuotientBySquare Y.toRingedSpace (𝓘)) ⟶
      (modulePullback i.toLRSHom.toShHom).obj (𝓘).toSheafOfModules :=
  ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _).symm
    (cokernel.desc (Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘))
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app (𝓘).toSheafOfModules)
      (idealSquareInclusion_comp_unit i))

/-- **`i^* (𝓘/𝓘²) ≅ i^* 𝓘`**: the pullback of the projection `𝓘 ⟶ 𝓘/𝓘²` is invertible, the
pullback being right exact and killing `𝓘² ⟶ 𝓘`. The inverse is built from the adjunction, so
that no preservation of zero morphisms has to be named. -/
def modulePullbackIdealQuotientBySquareIso :
    (modulePullback i.toLRSHom.toShHom).obj (𝓘).toSheafOfModules ≅
      (modulePullback i.toLRSHom.toShHom).obj
        (Stacks.Duality.idealQuotientBySquare Y.toRingedSpace (𝓘)) where
  hom := (modulePullback i.toLRSHom.toShHom).map
    (cokernel.π (Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘)))
  inv := modulePullbackIdealQuotientBySquareInv i
  hom_inv_id := by
    let adj := modulePullbackPushforwardAdjunction i.toLRSHom.toShHom
    refine (adj.homEquiv _ _).injective ?_
    exact ((adj.homEquiv_naturality_left _ _).trans
      (congrArg (fun g => cokernel.π (Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘)) ≫ g)
        (Equiv.apply_symm_apply _ _))).trans
      ((cokernel.π_desc _ _ _).trans (adj.homEquiv_id _).symm)
  inv_hom_id := by
    let adj := modulePullbackPushforwardAdjunction i.toLRSHom.toShHom
    refine (adj.homEquiv _ _).injective ?_
    refine ((adj.homEquiv_naturality_right _ _).trans
      (congrArg (fun g => g ≫ (modulePushforward i.toLRSHom.toShHom).map
        ((modulePullback i.toLRSHom.toShHom).map
          (cokernel.π (Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘)))))
        (Equiv.apply_symm_apply _ _))).trans (Eq.trans ?_ (adj.homEquiv_id _).symm)
    have : Epi (cokernel.π (Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘))) :=
      coequalizer.π_epi
    refine (cancel_epi (cokernel.π (Stacks.Duality.idealSquareInclusion Y.toRingedSpace (𝓘)))).1 ?_
    exact (cokernel.π_desc_assoc _ _ _ _).trans (adj.unit.naturality _).symm

/-- The categorical kernel `Stacks.ClosedImmersion.idealSheaf` of the comorphism of `i` is the
defining ideal sheaf. -/
@[no_expose] def idealSheafIsoDefiningIdeal :
    Stacks.ClosedImmersion.idealSheaf (Stacks.Duality.closedQuotient i).i ≅ (𝓘).toSheafOfModules :=
  (kernelIsKernel _).conePointUniqueUpToIso
    (Stacks.AlgebraicGeometry.kernelSubmodule_isLimit
      (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (Stacks.Duality.closedQuotient i).i)))

/-- The conormal sheaf of the closed immersion, computed through its `liftCoborder`
factorization, is `i^* 𝓘`. -/
def conormalSheafIsoPullbackDefiningIdeal :
    (modulePullback i.liftCoborder.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom) ≅
      (modulePullback (Stacks.Duality.closedQuotient i).i).obj (𝓘).toSheafOfModules :=
  (Stacks.ClosedImmersion.pullbackIdealSheafIso _ i.coborderRange.ι.toLRSHom.toShHom
      i.toLRSHom.toShHom
      (show (i.liftCoborder ≫ i.coborderRange.ι).toLRSHom.toShHom = _ by
        rw [Scheme.Hom.liftCoborder_ι])).symm ≪≫
    (modulePullback (Stacks.Duality.closedQuotient i).i).mapIso (idealSheafIsoDefiningIdeal i)

/-- **`𝓘/𝓘² ≅ i_* i^* 𝓘`**: the conormal quotient is a direct image, so it is `i_* i^*` of itself,
and `i^*` does not see the difference between `𝓘/𝓘²` and `𝓘`. -/
def idealQuotientBySquareIsoPushforward :
    Stacks.Duality.idealQuotientBySquare Y.toRingedSpace (𝓘) ≅
      (modulePushforward (Stacks.Duality.closedQuotient i).i).obj
        ((modulePullback (Stacks.Duality.closedQuotient i).i).obj (𝓘).toSheafOfModules) :=
  @asIso _ _ _ _ ((modulePullbackPushforwardAdjunction (Stacks.Duality.closedQuotient i).i).unit.app
      (Stacks.Duality.idealQuotientBySquare Y.toRingedSpace (𝓘)))
      (isIso_unit_idealQuotientBySquare i) ≪≫
    (modulePushforward (Stacks.Duality.closedQuotient i).i).mapIso
      (modulePullbackIdealQuotientBySquareIso i).symm

/-- `𝓗om(i_* 𝒪_X, i_* 𝒪_X) ≅ 𝒪_X` with exact support: the unit of `i_* ⊣ 𝓗om(𝒪_X, -)` at
`𝒪_X` is invertible, `i_*` being fully faithful. -/
instance isIso_unit_sheafHomExactSupport :
    IsIso
      ((Stacks.Duality.closedQuotient i).modulePushforwardSheafHomExactSupportAdjunction.unit.app
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))) := by
  have := @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _
    (Stacks.Duality.closedQuotient i).modulePushforwardSheafHomExactSupportAdjunction
    (Stacks.Duality.closedQuotient i).full_modulePushforward
    (Stacks.Duality.closedQuotient i).faithful_modulePushforward
  exact NatIso.isIso_app_of_isIso _ _

/-- **The two normal sheaves agree**: the normal sheaf `𝓗om_{𝒪_Y}(𝓘/𝓘², 𝒪_Y/𝓘)` of the defining
ideal sheaf of a closed immersion is the direct image `i_* 𝒩` of the normal sheaf
`𝒩 = 𝓗om_{𝒪_X}(𝒞_{X/Y}, 𝒪_X)` of the immersion. Through `𝓘/𝓘² ≅ i_* 𝒞_{X/Y}` and
`𝒪_Y/𝓘 ≅ i_* 𝒪_X` this is the underived form of [Stacks, Tag 0E2I],
`𝓗om_{𝒪_Y}(i_* N, F) ≅ i_* 𝓗om_{𝒪_X}(N, 𝓗om(𝒪_X, F))`, at `F = i_* 𝒪_X`, where the sheaf Hom with
exact support is `𝒪_X` again. -/
@[no_expose] def normalSheafOfIdealSheafIsoPushforward :
    Stacks.Duality.normalSheafOfIdealSheaf Y.toRingedSpace (𝓘) ≅
      (modulePushforward (Stacks.Duality.closedQuotient i).i).obj (Stacks.Divisors.normalSheaf i) :=
  Stacks.SheafOfModules.sheafHomIsoLeft _ _ _ (idealQuotientBySquareIsoPushforward i) ≪≫
    (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor
      (Stacks.Duality.closedQuotient i).siteX
      (Stacks.Duality.closedQuotient i).X.sheaf
      ((modulePushforward (Stacks.Duality.closedQuotient i).i).obj
        ((modulePullback (Stacks.Duality.closedQuotient i).i).obj (𝓘).toSheafOfModules))).mapIso
      (@Stacks.AlgebraicGeometry.kernelQuotientIso_of_epi _ _ _ _ _ _
        (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (Stacks.Duality.closedQuotient i).i))
        (Scheme.Modules.epi_unitToPushforwardObjUnit i)) ≪≫
    ((Stacks.Duality.closedQuotient i).sheafHomPushforwardNatIso
      ((modulePullback (Stacks.Duality.closedQuotient i).i).obj (𝓘).toSheafOfModules)).app
      ((modulePushforward (Stacks.Duality.closedQuotient i).i).obj
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))) ≪≫
    (modulePushforward (Stacks.Duality.closedQuotient i).i).mapIso
      ((Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor
        (Stacks.Duality.closedQuotient i).siteZ (Stacks.Duality.closedQuotient i).Z.sheaf
        ((modulePullback (Stacks.Duality.closedQuotient i).i).obj (𝓘).toSheafOfModules)).mapIso
        (@asIso _ _ _ _
          ((Adjunction.unit
            (Stacks.Duality.closedQuotient i).modulePushforwardSheafHomExactSupportAdjunction).app
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace)))
          (isIso_unit_sheafHomExactSupport i)).symm) ≪≫
    (modulePushforward (Stacks.Duality.closedQuotient i).i).mapIso
      (Stacks.SheafOfModules.dualSheafIso _ _ (conormalSheafIsoPullbackDefiningIdeal i).symm)

/-- **The exterior algebra of `i_* 𝒩` over `𝒪_Y/𝓘`, given the identification of the normal
sheaves.** If the normal sheaf `𝓗om(𝓘/𝓘², 𝒪_Y/𝓘)` of the defining ideal sheaf is `i_* 𝒩` as an
`𝒪_Y`-module, then the pushforward of the exterior algebra of `𝒩`, read over `𝒪_Y/𝓘` through
`𝒪_Y/𝓘 ≅ i_* 𝒪_X`, is an exterior algebra of the normal sheaf over `𝒪_Y/𝓘` whose pieces are the
`i_* ⋀ⁿ𝒩`. -/
theorem exists_exteriorAlgebra_pushforward_iso_of_iso
    (e : Stacks.Duality.normalSheafOfIdealSheaf Y.toRingedSpace (definingIdealOfHom i) ≅
      (modulePushforward (Stacks.Duality.closedQuotient i).i).obj (Stacks.Divisors.normalSheaf i)) :
    ∃ (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
        (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology Y.carrier)
          (Stacks.Sites.quotientRingSheaf.{u, u, u} (definingIdealOfHom i))))
      (ι : normalSheafQuotient (definingIdealOfHom i) ⟶ A.piece 1),
      _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι ∧
      ∀ n : ℤ, Nonempty
        ((_root_.SheafOfModules.restrictScalars
            (Stacks.Sites.quotientRingHom (definingIdealOfHom i))).obj (A.piece n) ≅
          (modulePushforward (Stacks.Duality.closedQuotient i).i).obj
            (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) n)) := by
  let : Sheaf.IsLocallySurjective (Stacks.Sites.quotientRingHom (definingIdealOfHom i)) :=
    Stacks.Sites.isLocallySurjective_quotientRingHom (definingIdealOfHom i)
  have (n : ℕ) : IsIso (pushforwardSheafifyHom (Opens.grothendieckTopology Y)
      (Opens.map i.base) (toRingCat (Opens.grothendieckTopology X) X.sheaf)
      (extPow n (Stacks.Divisors.normalSheaf i).val)) :=
    isIso_pushforwardSheafifyHom_of_isClosedEmbedding i.base i.isClosedEmbedding X.sheaf _
  have hP := SheafOfModules.ContinuousPushforward.isExteriorAlgebra_pushforward
    (Opens.grothendieckTopology Y)
    (Opens.map i.base) (Osharp := X.sheaf) (Stacks.Divisors.normalSheaf i)
    (Scheme.Modules.exteriorAlgebra _) (Scheme.Modules.exteriorGenerator _)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
  have hA := SheafOfModules.GradedAlgebra.IsExteriorAlgebra.scalarRestrict_of_iso
    (quotientRingSheafRingIso i) hP
  let c := fun N => SheafOfModules.restrictScalarsCompIso _ _ _
    (quotientRingHom_comp_quotientRingSheafRingIso_hom i)
    ((sheafPushforwardFunctor (Opens.grothendieckTopology Y) (Opens.map i.base)
      (toRingCat (Opens.grothendieckTopology X) X.sheaf)).obj N)
  let e' : normalSheafQuotient (definingIdealOfHom i) ≅
      (_root_.SheafOfModules.restrictScalars (quotientRingSheafRingIso i).hom).obj
        ((sheafPushforwardFunctor (Opens.grothendieckTopology Y) (Opens.map i.base)
          (toRingCat (Opens.grothendieckTopology X) X.sheaf)).obj
            (Stacks.Divisors.normalSheaf i)) :=
    (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (Stacks.Sites.quotientRingHom (definingIdealOfHom i))).preimageIso
      (Stacks.SheafOfModules.ChangeOfRings.restrictScalarsLiftedSheafIso
          (Stacks.Sites.quotientRingHom (definingIdealOfHom i))
          (Stacks.Duality.normalSheafOfIdealSheaf Y.toRingedSpace (definingIdealOfHom i))
          (smul_normalSheaf_eq_zero (definingIdealOfHom i)) ≪≫ e ≪≫
        (c (Stacks.Divisors.normalSheaf i)).symm)
  exact ⟨_, e'.hom ≫ _, SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso hA e'.hom
    inferInstance, fun n => ⟨c (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) n)⟩⟩

/-- **The exterior algebra of the normal sheaf of a closed immersion, pushed forward.** For a
closed immersion `i : X ⟶ Y` with defining ideal sheaf `𝓘`, there is an exterior algebra `A` over
`𝒪_Y/𝓘` of the normal sheaf `𝓗om_{𝒪_Y}(𝓘/𝓘², 𝒪_Y/𝓘)` of `𝓘` whose degree-`n` piece, read over
`𝒪_Y`, is the direct image `i_* ⋀ⁿ𝒩` of the `n`-th exterior power of the normal sheaf `𝒩` of
`i`. -/
theorem exists_exteriorAlgebra_pushforward_iso :
    ∃ (A : _root_.SheafOfModules.GradedAlgebra.{u, u}
        (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology Y.carrier)
          (Stacks.Sites.quotientRingSheaf.{u, u, u} (definingIdealOfHom i))))
      (ι : normalSheafQuotient (definingIdealOfHom i) ⟶ A.piece 1),
      _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι ∧
      ∀ n : ℤ, Nonempty
        ((_root_.SheafOfModules.restrictScalars
            (Stacks.Sites.quotientRingHom (definingIdealOfHom i))).obj (A.piece n) ≅
          (RingedSpaceModuleAdjunction.modulePushforward
            (Stacks.Duality.closedQuotient i).i).obj
            (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) n)) :=
  exists_exteriorAlgebra_pushforward_iso_of_iso i (normalSheafOfIdealSheafIsoPushforward i)

end Stacks.Duality.KoszulRegular

end
