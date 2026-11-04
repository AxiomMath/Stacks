module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperTransfer

/-!
# The comparison `X_{/T} ⟶ W` is bijective on locally Noetherian schemes

In a contraction situation `AlgebraicGeometry.Artin.ContractionSituation`, let `X` be a presheaf
on the big fppf site of `S` carrying a functorial bijection `F(V) = Mor_S(V, X)` on the locally
Noetherian schemes `V` over `S`, where `F` is Artin's functor, and let
`T ⊆ |X|` be `AlgebraicGeometry.Artin.ContractionSituation.contractedLocus`. The comparison
morphism `AlgebraicGeometry.Artin.ContractionSituation.completionToW` from the sections of `X`
with point-set image in `T` to `W` is an isomorphism of functors on locally Noetherian schemes
over `S`: `X_{/T}` agrees with `W` as a functor.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.tripleOfSection`: the element
  `(|V|, ∅ ⟶ U', w : V ⟶ W)` of `F(V)` attached to a section `w` of `W` over `V`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_univ`: for a
  section `w` of `W` over `V` the triple `(|V|, ∅ ⟶ U', w)` satisfies the compatibility
  condition.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.eq_of_Z_eq_univ`: a triple whose closed
  subset is all of `|V|` is determined by the section of `W` it gives.
* `AlgebraicGeometry.Artin.ContractionSituation.completionToW_app_injective`,
  `AlgebraicGeometry.Artin.ContractionSituation.completionToW_app_surjective` and
  `AlgebraicGeometry.Artin.ContractionSituation.isIso_completionToW`: the comparison morphism is
  bijective on every locally Noetherian scheme over `S`, that is, `X_{/T}` and `W` agree as
  functors on locally Noetherian schemes over `S`.

## References

* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### Objects covered by the empty sieve -/

/-- The sieve of a section cut out by the bottom subfunctor is the empty sieve. -/
theorem sieveOfSection_bot {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : (BigFppfOver B S hS)ᵒᵖ} (s : F.obj U) :
    (⊥ : Subfunctor F).sieveOfSection s = ⊥ := by
  ext V f
  exact iff_of_false (fun h => h) (fun h => h)

/-- A section of the sheafified bottom subfunctor lives over an object covered by the empty
sieve. -/
theorem bot_mem_of_mem_sheafify_bot {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : (BigFppfOver B S hS)ᵒᵖ} {s : F.obj U}
    (hs : s ∈ ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)).obj U) :
    (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop := by
  have h : (⊥ : Subfunctor F).sieveOfSection s ∈ BigFppfOver.topology B S hS U.unop := hs
  rwa [sieveOfSection_bot] at h

/-- A section of the subfunctor cut out by the empty set of points lives over an object
covered by the empty sieve: that subfunctor is the sheafified bottom subfunctor. -/
theorem bot_mem_of_mem_openSubspaceOfPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : Set (points B S hS F)} (hW : W = ∅) {U : (BigFppfOver B S hS)ᵒᵖ} {s : F.obj U}
    (hs : s ∈ (openSubspaceOfPoints B S hS F W).obj U) :
    (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop := by
  subst hW
  rw [openSubspaceOfPoints_empty] at hs
  exact bot_mem_of_mem_sheafify_bot B S hS hs

/-- An fppf sheaf has at most one section over an object covered by the empty sieve. -/
theorem subsingleton_of_bot_mem {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {U : (BigFppfOver B S hS)ᵒᵖ}
    (hU : (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop) :
    Subsingleton (G.obj U) :=
  let := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover ⟨G, hG⟩ U.unop hU)
  inferInstance

/-- An fppf sheaf has a section over an object covered by the empty sieve. -/
theorem nonempty_of_bot_mem {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {U : (BigFppfOver B S hS)ᵒᵖ}
    (hU : (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop) :
    Nonempty (G.obj U) :=
  let := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover ⟨G, hG⟩ U.unop hU)
  inferInstance

/-- Two morphisms into a presheaf with at most one section over every object covered by the
empty sieve agree, as soon as the source has sections only over such objects. -/
theorem hom_ext_of_bot_mem {Q G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hG : ∀ U : (BigFppfOver B S hS)ᵒᵖ,
      (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop → Subsingleton (G.obj U))
    (hQ : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (_ : Q.obj U),
      (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop)
    (a b : Q ⟶ G) : a = b := by
  ext U q
  exact (hG U (hQ U q)).elim _ _

/-- An object covered by the empty sieve has no points. -/
theorem isEmpty_points_yoneda_of_bot_mem {U : BigFppfOver B S hS}
    (hU : (⊥ : Sieve U) ∈ BigFppfOver.topology B S hS U) :
    IsEmpty (points B S hS (yoneda.obj U)) := by
  have hs : (𝟙 U : (yoneda.obj U).obj (op U)) ∈
      ((⊥ : Subfunctor (yoneda.obj U)).sheafify (BigFppfOver.topology B S hS)).obj (op U) := by
    show (⊥ : Subfunctor (yoneda.obj U)).sieveOfSection (𝟙 U) ∈ BigFppfOver.topology B S hS U
    rwa [sieveOfSection_bot]
  exact ⟨fun q => (isEmpty_points_sheafify_bot B S hS (yoneda.obj U)).false
    (pointsMap B S hS (yoneda.obj U) (yonedaEquiv.symm ⟨𝟙 U, hs⟩) q)⟩

/-- The morphism into a subspace `G_{W'}` cut out by a set of points of an fppf sheaf `G`
from a presheaf having sections only over objects covered by the empty sieve: over such an
object `G` has exactly one section, and it lies in `G_{W'}` since the object has no points. -/
noncomputable def homOfBotMem {Q G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) (W' : Set (points B S hS G))
    (hQ : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (_ : Q.obj U),
      (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop) :
    Q ⟶ (openSubspaceOfPoints B S hS G W').toFunctor where
  app U := ↾fun q =>
    haveI := nonempty_of_bot_mem B S hS hG (hQ U q)
    ⟨Classical.arbitrary _, by
      have := isEmpty_points_yoneda_of_bot_mem B S hS (hQ U q)
      rw [mem_openSubspaceOfPoints_iff, Set.range_eq_empty]
      exact Set.empty_subset _⟩
  naturality U V f := by
    ext q
    exact Subtype.ext ((subsingleton_of_bot_mem B S hS hG (hQ V (Q.map f q))).elim _ _)

/-- The morphism into an fppf sheaf from a presheaf having sections only over objects covered
by the empty sieve. -/
noncomputable def toSheafOfBotMem {Q G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hQ : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (_ : Q.obj U),
      (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop) :
    Q ⟶ G :=
  homOfBotMem B S hS hG Set.univ hQ ≫ (openSubspaceOfPoints B S hS G Set.univ).ι

/-! ### The completion along all points -/

/-- The completion of a presheaf along all of its points maps isomorphically onto the
sheafified universe lift: every section has point-set image in the whole space of points. -/
theorem isIso_completionSheafInclusion (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {T : Set (points B S hS X)} (hT : T = Set.univ) :
    IsIso (completionSheafInclusion B S hS X T) := by
  have : IsIso (completionSubfunctor B S hS X T).ι := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun U => ?_)
    rw [isIso_iff_bijective]
    refine ⟨fun a b h => Subtype.ext h, fun x => ⟨⟨x, ?_⟩, rfl⟩⟩
    subst hT
    exact hasImageIn_univ B S hS X U.unop x.down
  rw [completionSheafInclusion_eq_map]
  exact Functor.map_isIso _ _

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- The completion of the representable presheaf of `V` along all of `|V|` is the scheme `V`
itself, as an fppf sheaf. -/
noncomputable def completionSheafUnivIso (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) :
    Space.completionSheaf B S hS (yoneda.obj V) Z ≅ schemeSheaf B S hS V :=
  haveI := Space.isIso_completionSheafInclusion B S hS (yoneda.obj V) hZ
  asIso (Space.completionSheafInclusion B S hS (yoneda.obj V) Z) ≪≫
    ObjectProperty.isoMk _ (Space.sheafifiedULiftIso B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V).isSheaf).symm

/-- A morphism `V_{/V} = V ⟶ 𝔜` into a formal algebraic space is representable by algebraic
spaces. -/
theorem isRepresentable_completionIdHom (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) {Y : FppfSheaf B S hS}
    (hY : IsFormalAlgebraicSpace B S hS Y) (y : Y.obj.obj (op V)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (completionIdHom B S hS V Z hZ y).hom :=
  isRepresentableByAlgebraicSpacesULift_of_isAlgebraicSpaceULift_of_isFormal B S hS _
    (Space.isAlgebraicSpaceULift_of_iso B S hS
      ((sheafToPresheaf _ _).mapIso (completionSheafUnivIso B S hS V hZ).symm)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V)) hY

end FormalSpace

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

attribute [local instance] Space.pointTopology

/-! ### The triple attached to a section of `W` -/

/-- The unique morphism from the empty open subspace `V ∖ |V|` into `U'`. -/
noncomputable def emptyToSituationOpen (V : BigFppfOver B S hS)
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor :=
  Space.homOfBotMem B S hS c.isAlgebraicSpace_X'.isSheaf c.T'ᶜ fun _ s =>
    Space.bot_mem_of_mem_openSubspaceOfPoints B S hS (by rw [hZ, Set.compl_univ]) s.2

/-- `U'` has at most one section over an object covered by the empty sieve. -/
theorem subsingleton_U'_of_bot_mem {U : (BigFppfOver B S hS)ᵒᵖ}
    (hU : (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop) :
    Subsingleton (c.U'.toFunctor.obj U) :=
  ⟨fun _ _ => Subtype.ext
    ((Space.subsingleton_of_bot_mem B S hS c.isAlgebraicSpace_X'.isSheaf hU).elim _ _)⟩

/-- For a section `w` of `W` over `V`, the triple `(|V|, ∅ ⟶ U', w : V_{/V} = V ⟶ W)` satisfies
the compatibility condition: it has a `CompatibilityWitness`. -/
theorem nonempty_compatibilityWitness_univ (V : BigFppfOver B S hS)
    (w : c.W.obj.obj (op V)) :
    Nonempty (CompatibilityWitness c V Set.univ (emptyToSituationOpen c V rfl)
      (FormalSpace.completionIdHom B S hS V Set.univ rfl w)) := by
  classical
  let eV := FormalSpace.completionSheafUnivIso B S hS V
    (Z := (Set.univ : Set (Space.points B S hS (yoneda.obj V)))) rfl
  let ξ : FormalSpace.schemeSheaf B S hS V ⟶ c.W :=
    eV.inv ≫ FormalSpace.completionIdHom B S hS V Set.univ rfl w
  have sq := IsPullback.of_hasPullback ξ c.g
  obtain ⟨hrep, hprop⟩ :=
    FormalSpace.IsProper.of_isPullback B S hS sq c.isFormalModification_g.isProper
  have hP : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ c.g).obj :=
    Space.isAlgebraicSpaceULift_of_isRepresentable_uliftYoneda.{u + 1} B S hS
      (pullback.fst ξ c.g).hom (Iso.refl _) hrep
  have hVL : Space.IsAlgebraicSpaceULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj V) :=
    Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V
  have hfst : Space.IsProperULift.{u + 1} B S hS (pullback.fst ξ c.g).hom := by
    have hcomp : (IsPullback.of_id_snd (f := (pullback.fst ξ c.g).hom)).isoPullback.hom ≫
        pullback.fst (𝟙 _) (pullback.fst ξ c.g).hom = (pullback.fst ξ c.g).hom :=
      IsPullback.isoPullback_hom_fst _
    rw [← hcomp]
    exact Space.isProperULift_precomp.{u + 1} B S hS _ _ hP (hrep V (𝟙 _)) hVL
      (hprop V (𝟙 _))
  obtain ⟨V₀, hV₀, ⟨e₀⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift.{u + 1} B S hS hP
  let ff : ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).FullyFaithful :=
    fullyFaithfulULiftFunctor.whiskeringRight _
  let p₀ : V₀ ⟶ yoneda.obj V := ff.preimage (e₀.hom ≫ (pullback.fst ξ c.g).hom)
  have hp₀ : Functor.whiskerRight p₀ uliftFunctor.{u + 1} =
      e₀.hom ≫ (pullback.fst ξ c.g).hom :=
    ff.map_preimage _
  let sX' := Space.sheafifiedULiftIso B S hS c.X' c.isAlgebraicSpace_X'.isSheaf
  let x₀ : V₀ ⟶ c.X' := ff.preimage (e₀.hom ≫ (pullback.snd ξ c.g).hom ≫
    (Space.completionSheafInclusion B S hS c.X' c.T').hom ≫ sX'.inv)
  have hx₀ : Functor.whiskerRight x₀ uliftFunctor.{u + 1} = e₀.hom ≫
      (pullback.snd ξ c.g).hom ≫ (Space.completionSheafInclusion B S hS c.X' c.T').hom ≫
        sX'.inv :=
    ff.map_preimage _
  have hV₀L : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (V₀ ⋙ uliftFunctor.{u + 1}) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff.{u + 1} B S hS V₀).mpr hV₀
  have hproper : Space.IsProper B S hS p₀ := by
    rw [← Space.isProperULift_whiskerRight_iff.{u + 1} B S hS p₀, hp₀]
    exact Space.isProperULift_precomp.{u + 1} B S hS e₀ _ hV₀L hP hVL hfst
  have hT₀ : Space.pointsMap B S hS V₀ p₀ ⁻¹'
      (Set.univ : Set (Space.points B S hS (yoneda.obj V))) = Set.univ :=
    Set.preimage_univ
  have := Space.isIso_completionSheafInclusion B S hS V₀ hT₀
  let sV₀ := Space.sheafifiedULiftIso B S hS V₀ hV₀.isSheaf
  let e' : Space.completionSheaf B S hS V₀ (Space.pointsMap B S hS V₀ p₀ ⁻¹' Set.univ) ≅
      pullback ξ c.g :=
    asIso (Space.completionSheafInclusion B S hS V₀ _) ≪≫
      ObjectProperty.isoMk _ (sV₀.symm ≪≫ e₀)
  have hempty : (Set.univ : Set (Space.points B S hS (yoneda.obj V)))ᶜ = ∅ := Set.compl_univ
  have hE : ∀ (U : (BigFppfOver B S hS)ᵒᵖ)
      (_ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V)
        (Set.univ : Set (Space.points B S hS (yoneda.obj V)))ᶜ).toFunctor.obj U),
      (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop :=
    fun _ s => Space.bot_mem_of_mem_openSubspaceOfPoints B S hS hempty s.2
  let j := Space.toSheafOfBotMem B S hS hV₀.isSheaf hE
  have hext : ∀ {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) G →
      ∀ a b : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Set.univᶜ).toFunctor ⟶ G,
        a = b :=
    fun hG => Space.hom_ext_of_bot_mem B S hS
      (fun _ hU => Space.subsingleton_of_bot_mem B S hS hG hU) hE
  have hw : 𝟙 _ ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Set.univᶜ).ι =
      j ≫ p₀ := hext (isAlgebraicSpace_yoneda B S hS V).isSheaf _ _
  let sY := Space.sheafifiedULiftIso B S hS (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS V).isSheaf
  have hp₀' : (Space.sheafifiedULiftMap B S hS p₀).hom =
      sV₀.inv ≫ (e₀.hom ≫ (pullback.fst ξ c.g).hom) ≫ sY.hom := by
    rw [Space.sheafifiedULiftMap_hom_eq B S hS hV₀.isSheaf
      (isAlgebraicSpace_yoneda B S hS V).isSheaf p₀, hp₀]
    rfl
  have hkey : Space.sheafifiedULiftMap B S hS p₀ ≫
      (ObjectProperty.isoMk _ sY.symm : _ ≅ FormalSpace.schemeSheaf B S hS V).hom =
      (ObjectProperty.isoMk _ (sV₀.symm ≪≫ e₀) : _ ≅ pullback ξ c.g).hom ≫
        pullback.fst ξ c.g := by
    rw [← Iso.eq_comp_inv]
    apply Sheaf.hom_ext
    rw [hp₀']
    rfl
  have hC1 : Space.completionSheafRestrict B S hS p₀ _ Set.univ Set.Subset.rfl ≫ eV.hom =
      e'.hom ≫ pullback.fst ξ c.g := by
    have h₁ := Space.completionSheafRestrict_comp_inclusion B S hS p₀
      (Space.pointsMap B S hS V₀ p₀ ⁻¹' Set.univ) Set.univ Set.Subset.rfl
    simp only [eV, e', FormalSpace.completionSheafUnivIso, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, h₁, Category.assoc, hkey, Category.assoc]
  have hx₀' : (Space.sheafifiedULiftMap B S hS x₀).hom =
      sV₀.inv ≫ e₀.hom ≫ (pullback.snd ξ c.g).hom ≫
        (Space.completionSheafInclusion B S hS c.X' c.T').hom := by
    rw [Space.sheafifiedULiftMap_hom_eq B S hS hV₀.isSheaf c.isAlgebraicSpace_X'.isSheaf x₀,
      hx₀]
    simp only [sX', Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hkey₂ : Space.sheafifiedULiftMap B S hS x₀ =
      (ObjectProperty.isoMk _ (sV₀.symm ≪≫ e₀) : _ ≅ pullback ξ c.g).hom ≫
        pullback.snd ξ c.g ≫ Space.completionSheafInclusion B S hS c.X' c.T' := by
    apply Sheaf.hom_ext
    rw [hx₀']
    rfl
  refine ⟨{ V' := V₀
            isAlgebraicSpace_V' := hV₀
            p := p₀
            isProper_p := hproper
            j := j
            isPullback_j := ?_
            xhat' := e'.hom ≫ pullback.snd ξ c.g
            isPullback_xhat' := ?_
            x' := x₀
            restrict_x' := ?_
            completion_x' := ?_ }⟩
  · refine IsPullback.of_forall_isPullback_app fun U => ?_
    refine (Types.isPullback_iff _ _ _ _).2 ⟨congrArg (fun φ => φ.app U) hw,
      fun a b h => h.1, fun a b _ => ⟨a, rfl, ?_⟩⟩
    exact (Space.subsingleton_of_bot_mem B S hS hV₀.isSheaf (hE U a)).elim _ _
  · refine IsPullback.of_iso sq e'.symm eV.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← hC1,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact hext c.isAlgebraicSpace_X'.isSheaf _ _
  · rw [hkey₂]
    simp only [e', Iso.trans_hom, asIso_hom, Category.assoc]

/-- The element `(|V|, ∅ ⟶ U', w)` of `F(V)` attached to a section `w` of `W` over `V`: its
closed subset is all of `|V|`, its second component is the unique morphism out of the empty
open subspace, and its third component is the morphism `V_{/V} = V ⟶ W` given by `w`. -/
noncomputable def tripleOfSection (V : BigFppfOver B S hS) (w : c.W.obj.obj (op V)) :
    Triple c V where
  Z := Set.univ
  isClosed_Z := isClosed_univ
  u := emptyToSituationOpen c V rfl
  xhat := FormalSpace.completionIdHom B S hS V Set.univ rfl w
  adic_xhat := FormalSpace.isRepresentable_completionIdHom B S hS V rfl
    c.isLocallyNoetherian_W.1 w
  compatible := nonempty_compatibilityWitness_univ c V w

/-- The section of `W` determined by the triple attached to a section `w` is `w`. -/
theorem wSection_tripleOfSection (V : BigFppfOver B S hS) (w : c.W.obj.obj (op V)) :
    wSection c (tripleOfSection c V w) rfl = w :=
  FormalSpace.completionIdHom_completionIdSection B S hS V Set.univ rfl w

/-- A triple whose closed subset is all of `|V|` is determined by the section of `W` it
determines. -/
theorem Triple.eq_of_Z_eq_univ {V : BigFppfOver B S hS} (t t' : Triple c V)
    (ht : t.Z = Set.univ) (ht' : t'.Z = Set.univ) (h : wSection c t ht = wSection c t' ht') :
    t = t' := by
  obtain ⟨Z, hZc, u, x, a, w⟩ := t
  obtain ⟨Z', hZc', u', x', a', w'⟩ := t'
  dsimp only at ht ht'
  subst ht ht'
  refine Triple.mk_congr rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · refine Space.hom_ext_of_bot_mem B S hS (fun _ hU => subsingleton_U'_of_bot_mem c hU) ?_ _ _
    exact fun _ s => Space.bot_mem_of_mem_openSubspaceOfPoints B S hS Set.compl_univ s.2
  · exact FormalSpace.completionSheaf_hom_ext_of_univ B S hS Set.univ rfl h

/-! ### Bijectivity of the comparison map -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

/-- The triple matched with the section of `X` corresponding to a triple is that triple. -/
theorem tripleOfMor_yonedaEquiv_symm_hom_app (V : LocallyNoetherianOver B S hS)
    (t : Triple c V.obj) :
    tripleOfMor c α V (yonedaEquiv.symm (α.hom.app (op V) t).down) = t := by
  simp only [tripleOfMor, Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (α.hom_inv_id_app (op V)) t

/-- The comparison `X_{/T} ⟶ W` is injective on every locally Noetherian scheme over `S`. -/
theorem completionToW_app_injective (V : (LocallyNoetherianOver B S hS)ᵒᵖ) :
    Function.Injective ((completionToW c α).app V) := by
  rintro ⟨⟨x⟩, hx⟩ ⟨⟨y⟩, hy⟩ h
  have h' : completionSectionToW c α V.unop x hx = completionSectionToW c α V.unop y hy := h
  have ht := Triple.eq_of_Z_eq_univ c _ _ ((hasImageIn_contractedLocus_iff c α V.unop x).mp hx)
    ((hasImageIn_contractedLocus_iff c α V.unop y).mp hy) h'
  simp only [tripleOfMor, Equiv.apply_symm_apply] at ht
  obtain rfl : x = y :=
    congrArg ULift.down (((isIso_iff_bijective (α.inv.app (op V.unop))).1 inferInstance).1 ht)
  rfl

/-- The comparison `X_{/T} ⟶ W` is surjective on every locally Noetherian scheme over `S`. -/
theorem completionToW_app_surjective (V : (LocallyNoetherianOver B S hS)ᵒᵖ) :
    Function.Surjective ((completionToW c α).app V) := by
  intro w
  let t := tripleOfSection c V.unop.obj w
  let x := (α.hom.app (op V.unop) t).down
  have hx : tripleOfMor c α V.unop (yonedaEquiv.symm x) = t :=
    tripleOfMor_yonedaEquiv_symm_hom_app c α V.unop t
  have hxT : Space.HasImageIn B S hS X (contractedLocus c α) V.unop.obj x :=
    (hasImageIn_contractedLocus_iff c α V.unop x).mpr (by rw [hx]; rfl)
  refine ⟨⟨ULift.up x, hxT⟩, ?_⟩
  show completionSectionToW c α V.unop x hxT = w
  rw [completionSectionToW, wSection_congr c hx _ rfl]
  exact wSection_tripleOfSection c V.unop.obj w

/-- The comparison morphism from the sections of `X` with point-set image in `T` to `W` is an
isomorphism of functors on the locally Noetherian schemes over `S`. -/
theorem isIso_completionToW : IsIso (completionToW c α) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun V => (isIso_iff_bijective _).2
    ⟨completionToW_app_injective c α V, completionToW_app_surjective c α V⟩

end Artin.ContractionSituation

end AlgebraicGeometry

end
