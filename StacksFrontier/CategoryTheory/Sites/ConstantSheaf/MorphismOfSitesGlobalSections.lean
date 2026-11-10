module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.ConstantInverseImage
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.AdjunctionVersusRestriction
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.PushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction along a morphism of sites does not change global sections

Let `u : A ⥤ B` be a continuous functor of sites whose inverse image `u⁻¹ = u.sheafPullback` on
sheaves of **sets** is left exact — in particular let `u` define a morphism of sites in the sense
of [Stacks, Tag 00X1], `CategoryTheory.Functor.IsMorphismOfSites`, whose
`preservesFiniteLimits` field says exactly that. Then restriction along `u` does not change
global sections:

`u_* ⋙ Γ(A, -) ≅ Γ(B, -)`.

The proof is the formal one and touches neither site: global sections of a sheaf of sets are the
morphisms out of the constant sheaf on a one-element set
(`CategoryTheory.Sheaf.ΓObjEquivHom`), that constant sheaf is a *final* sheaf
(`Stacks.ConstantSheaf.isTerminal_constantSheaf_obj`), a left exact `u⁻¹` carries a final sheaf
to a final sheaf (`Stacks.ConstantSheaf.inverseImageTerminalIso`), and the adjunction
`u⁻¹ ⊣ u_*` moves the Hom across.

## Why this is not one of the two statements already in the library

Both existing forms of "restriction does not change global sections" carry a hypothesis that an
inverse system of *affine* sites over a non-affine scheme cannot meet, which is what this file is
for.

* `Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal` is this statement with `[u.Final]`: for
  every object `X` of `B` the comma category of pairs `(V, u V ⟶ X)` is nonempty and connected.
  The transition functors of an inverse system of small affine etale sites are not final — a
  quasi-compact etale scheme over a level has no reason to admit a morphism to the base change of
  a *single* affine object upstairs, its image downstairs needing more than one affine open to
  cover it.
* `Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso` is this statement with a terminal
  object on both sites, and `Stacks.ConstantSheaf.pushforwardSectionsIso` is the same comparison
  for sections over two given terminal objects. A site of affine objects over a non-affine
  quasi-compact quasi-separated scheme has no terminal object; that absence is the entire reason
  the colimit-of-sites development exists.

Left exactness of `u⁻¹` is strictly weaker than finality and is *free* for the systems in
question: `CategoryTheory.Functor.IsMorphismOfSites` carries it as a field, and
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites` carries an
`IsMorphismOfSites` for every transition.

## Main results

* `Stacks.ConstantSheaf.gammaPushforwardEquiv` — the comparison of global sections, one sheaf at
  a time.
* `Stacks.ConstantSheaf.gammaCompPushforwardIso` — `u_* ⋙ Γ(A, -) ≅ Γ(B, -)`, natural in the
  sheaf on `(B, K)`, for a continuous `u` with left exact inverse image.
* `Stacks.ConstantSheaf.gammaCompPushforwardIsoOfMorphismOfSites` — the same for a `u` defining a
  morphism of sites, which is the form a consumer has.
* `Stacks.ConstantSheaf.ΓRes_gammaPushforwardEquiv`,
  `Stacks.ConstantSheaf.ΓRes_gammaCompPushforwardIso` and
  `Stacks.ConstantSheaf.ΓRes_gammaCompPushforwardIsoOfMorphismOfSites` — that comparison is
  compatible with `CategoryTheory.Sheaf.ΓRes`.

## Implementation notes

Only sheaves of **sets** are treated. For abelian sheaves the corresponding statement does not
follow formally from this one: `Sheaf.Γ` for abelian coefficients is corepresented by the constant
sheaf on `ℤ` rather than by a final sheaf, so the argument needs the *abelian* inverse image to
take the constant sheaf to the constant sheaf, and left exactness of the inverse image on sheaves
of sets does not say that. The two routes to the abelian case, neither carried out here, are
either to transport this isomorphism along the restriction maps — which needs the compatibility of
`CategoryTheory.Sheaf.ΓObjEquivHom` with `CategoryTheory.Sheaf.ΓRes`, a statement Mathlib does not
have — so as to identify `CategoryTheory.Sheaf.coneΓ` of the restriction as a limit cone and then
to use that `forget Ab` creates that limit; or to prove the abelian form of [Stacks, Tag 00XO]
directly, that the abelian inverse image takes `ℤ_A^♯` to `ℤ_B^♯`, for which
`Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf` and the fact
that the free abelian sheaf functor and the inverse image are both left adjoints are the inputs.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace Stacks.ConstantSheaf

section Pushforward

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  [HasGlobalSectionsFunctor J (Type w)] [HasGlobalSectionsFunctor K (Type w)]
  [(u.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]

/-- **Restriction along a morphism of sites does not change global sections**, one sheaf at a
time: `Γ(A, u_* H) ≃ Γ(B, H)`.

The chain is formal. Global sections are the morphisms out of the constant sheaf on a one-element
set (`CategoryTheory.Sheaf.ΓObjEquivHom`); the adjunction `u⁻¹ ⊣ u_*` turns those into morphisms
out of `u⁻¹` of that sheaf; and `Stacks.ConstantSheaf.inverseImageTerminalIso` identifies
`u⁻¹` of it with the constant sheaf on a one-element set downstairs, both being final sheaves and
`u⁻¹` being left exact. -/
public def gammaPushforwardEquiv (H : Sheaf K (Type w)) :
    (Sheaf.Γ J (Type w)).obj ((u.sheafPushforwardContinuous (Type w) J K).obj H) ≃
      (Sheaf.Γ K (Type w)).obj H :=
  (Sheaf.ΓObjEquivHom J _ (PUnit.{w + 1} : Type w)).trans
    (((u.sheafAdjunctionContinuous (Type w) J K).homEquiv
        ((constantSheaf J (Type w)).obj (PUnit.{w + 1} : Type w)) H).symm.trans
      ((Iso.homCongr (inverseImageTerminalIso (u.sheafPullback (Type w) J K)).symm
          (Iso.refl H)).trans
        (Sheaf.ΓObjEquivHom K H (PUnit.{w + 1} : Type w)).symm))

/-- `Stacks.ConstantSheaf.gammaPushforwardEquiv` is natural in the sheaf: each of the four steps
of the chain is. -/
public lemma gammaPushforwardEquiv_naturality {H H' : Sheaf K (Type w)} (φ : H ⟶ H')
    (s : (Sheaf.Γ J (Type w)).obj ((u.sheafPushforwardContinuous (Type w) J K).obj H)) :
    gammaPushforwardEquiv u J K H'
        ((Sheaf.Γ J (Type w)).map ((u.sheafPushforwardContinuous (Type w) J K).map φ) s) =
      (Sheaf.Γ K (Type w)).map φ (gammaPushforwardEquiv u J K H s) := by
  dsimp only [gammaPushforwardEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Iso.symm_inv]
  rw [Sheaf.ΓObjEquivHom_naturality, Adjunction.homEquiv_naturality_right_symm,
    ← Sheaf.ΓObjEquivHom_naturality_symm]
  refine congrArg _ ?_
  simp

/-- **Restriction along a morphism of sites does not change global sections**:

`u_* ⋙ Γ(A, -) ≅ Γ(B, -)`,

naturally in the sheaf of sets on `(B, K)`. Only continuity of `u` and left exactness of its
inverse image on sheaves of sets are used; neither site needs a terminal object and `u` need not
be final. -/
public def gammaCompPushforwardIso :
    u.sheafPushforwardContinuous (Type w) J K ⋙ Sheaf.Γ J (Type w) ≅ Sheaf.Γ K (Type w) :=
  NatIso.ofComponents (fun H => (gammaPushforwardEquiv u J K H).toIso) fun φ => by
    ext s
    exact gammaPushforwardEquiv_naturality u J K φ s

end Pushforward

/-! ### The comparison is compatible with restrictions

The comparison of this section is built from `CategoryTheory.Sheaf.ΓObjEquivHom` and the
inverse-image adjunction, and so says nothing about `CategoryTheory.Sheaf.ΓRes` on its face. It
*is* compatible with restrictions, and the proof needs neither of the two maps it is built from to
be computed: both land in the sections of a terminal sheaf, where any two elements agree.

This is for sheaves of **sets** only, and the abelian form does not follow from it. The abelian
comparison `gammaCompPushforwardIsoAb` is built instead from
`ModuleSheafCohomology.globalSectionsRepresentation` and from `pullbackConstantSheafIsoAb`, and
the forcing argument does not reach the latter: the constant abelian sheaf on `ℤ` is not a
terminal sheaf, so the component of that isomorphism — a composite of
`Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf`,
`pullbackFreeAbelianSheafIso` (an `CategoryTheory.Adjunction.leftAdjointUniq`) and
`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W` — would have to be computed.
-/

section PushforwardRestriction

variable {A : Type u} [Category.{v} A] {B : Type u} [Category.{v} B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  [HasGlobalSectionsFunctor J (Type w)] [HasGlobalSectionsFunctor K (Type w)]
  [(u.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]

/-- The constant sheaf on a one-element type has exactly one section over every object. -/
private theorem nonempty_unique_sections_constantSheaf_punit {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] (X : Cᵒᵖ) :
    Nonempty (Unique (((constantSheaf J (Type w)).obj (PUnit.{w + 1} : Type w)).obj.obj X)) :=
  ⟨Sheaf.unique_sections_of_isTerminal
    (isTerminal_constantSheaf_obj J (Type w) Types.isTerminalPUnit) X⟩

/-- **The comparison of global sections at a morphism of sites is compatible with
restrictions**: the restriction to `u V` of the global section of `H` that
`Stacks.ConstantSheaf.gammaPushforwardEquiv` produces from a global section `s` of `u_* H` is the
restriction of `s` to `V`, the two sections living in the same group because `u_*` is restriction
along `u.op`.

Neither of the two maps the comparison is built from has to be computed, and that is the whole
proof. Read as a morphism out of the constant sheaf on a one-element type and evaluated at an
object, a global section becomes its own restriction to that object
(`CategoryTheory.Sheaf.ΓObjEquivHom_hom_app_apply`), and the adjunct of the comparison's middle
map has component the unit of the inverse-image adjunction followed by the map itself
(`CategoryTheory.Sheaf.rightAdjunct_hom_app`). So both sides are the *same* map
`u⁻¹(PUnit_J) ⟶ H` evaluated at two sections of `u⁻¹(PUnit_J)` over `u V` — one reached through
the adjunction's unit, the other through the component of
`Stacks.ConstantSheaf.inverseImageTerminalIso` — and `u⁻¹` is left exact, so `u⁻¹(PUnit_J)` is a
terminal sheaf and those sections are a singleton
(`CategoryTheory.Sheaf.subsingleton_sections_of_isTerminal`). The two sections are therefore
equal, whatever they are, and neither map is ever computed.

No terminal object of either site is used, so this holds on the sites with none for which
`CategoryTheory.Sheaf.Γ` exists at all. -/
public lemma ΓRes_gammaPushforwardEquiv (H : Sheaf K (Type w)) (V : Aᵒᵖ)
    (s : (Sheaf.Γ J (Type w)).obj ((u.sheafPushforwardContinuous (Type w) J K).obj H)) :
    H.ΓRes (u.op.obj V) (gammaPushforwardEquiv u J K H s) =
      ((u.sheafPushforwardContinuous (Type w) J K).obj H).ΓRes V s := by
  obtain ⟨huJ⟩ := nonempty_unique_sections_constantSheaf_punit J V
  obtain ⟨huK⟩ := nonempty_unique_sections_constantSheaf_punit K (u.op.obj V)
  have hsub : Subsingleton
      (((u.sheafPullback (Type w) J K).obj
          ((constantSheaf J (Type w)).obj (PUnit.{w + 1} : Type w))).obj.obj (u.op.obj V)) :=
    Sheaf.subsingleton_sections_of_isTerminal
      (IsTerminal.isTerminalObj (u.sheafPullback (Type w) J K) _
        (isTerminal_constantSheaf_obj J (Type w) Types.isTerminalPUnit)) _
  rw [← Sheaf.ΓObjEquivHom_hom_app_apply (X := (PUnit.{w + 1} : Type w))
        (gammaPushforwardEquiv u J K H s) (u.op.obj V) default,
    ← Sheaf.ΓObjEquivHom_hom_app_apply (X := (PUnit.{w + 1} : Type w)) s V default]
  obtain ⟨ψ, hψ⟩ : ∃ ψ, (u.sheafAdjunctionContinuous (Type w) J K).homEquiv
      ((constantSheaf J (Type w)).obj (PUnit.{w + 1} : Type w)) H ψ =
      Sheaf.ΓObjEquivHom J ((u.sheafPushforwardContinuous (Type w) J K).obj H)
        (PUnit.{w + 1} : Type w) s := ⟨_, Equiv.apply_symm_apply _ _⟩
  dsimp only [gammaPushforwardEquiv, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply]
  simp only [Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  rw [← hψ, Equiv.symm_apply_apply]
  exact congrArg (ψ.hom.app (u.op.obj V)) (hsub.elim _ _)

/-- **The comparison of global sections at a morphism of sites is compatible with restrictions**,
as an equality of morphisms. `Stacks.ConstantSheaf.ΓRes_gammaPushforwardEquiv` read through
`Stacks.ConstantSheaf.gammaCompPushforwardIso`, whose component at `H` is that equivalence. -/
public lemma ΓRes_gammaCompPushforwardIso (H : Sheaf K (Type w)) (V : Aᵒᵖ) :
    (gammaCompPushforwardIso u J K).hom.app H ≫ H.ΓRes (u.op.obj V) =
      ((u.sheafPushforwardContinuous (Type w) J K).obj H).ΓRes V := by
  ext s
  exact ΓRes_gammaPushforwardEquiv u J K H V s

end PushforwardRestriction

section MorphismOfSites

variable {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)]
  [HasGlobalSectionsFunctor J (Type u)] [HasGlobalSectionsFunctor K (Type u)]

/-- **Restriction along a morphism of sites does not change global sections**, in the form a
consumer has it: the hypothesis is `CategoryTheory.Functor.IsMorphismOfSites`, [Stacks, Tag 00X1],
whose two fields are exactly the continuity and the left exactness that
`Stacks.ConstantSheaf.gammaCompPushforwardIso` asks for.

This is the form the transitions of an inverse system of sites satisfy:
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites` carries an `IsMorphismOfSites` for
every transition functor and for every functor to the colimit site, with no terminality and no
finality available. -/
public def gammaCompPushforwardIsoOfMorphismOfSites (hu : u.IsMorphismOfSites J K) :
    letI := hu.isContinuous
    u.sheafPushforwardContinuous (Type u) J K ⋙ Sheaf.Γ J (Type u) ≅ Sheaf.Γ K (Type u) :=
  let := hu.isContinuous
  let := hu.preservesFiniteLimits
  gammaCompPushforwardIso u J K

/-- **The comparison of global sections at a morphism of sites is compatible with restrictions**,
in the form a consumer has it: the hypothesis is
`CategoryTheory.Functor.IsMorphismOfSites`. This is
`Stacks.ConstantSheaf.ΓRes_gammaCompPushforwardIso` with the two instances read off that
hypothesis, exactly as `gammaCompPushforwardIsoOfMorphismOfSites` is
`gammaCompPushforwardIso`. -/
public lemma ΓRes_gammaCompPushforwardIsoOfMorphismOfSites (hu : u.IsMorphismOfSites J K)
    (H : Sheaf K (Type u)) (V : Aᵒᵖ) :
    letI := hu.isContinuous
    (gammaCompPushforwardIsoOfMorphismOfSites u J K hu).hom.app H ≫ H.ΓRes (u.op.obj V) =
      ((u.sheafPushforwardContinuous (Type u) J K).obj H).ΓRes V := by
  let := hu.isContinuous
  let := hu.preservesFiniteLimits
  exact ΓRes_gammaCompPushforwardIso u J K H V

end MorphismOfSites

/-! ### The inverse image of the constant abelian sheaf on `ℤ` -/

section ConstantSheafInverseImage

variable {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint]
  [(u.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback (Type u) J K)]

/-- The right adjoint of `ℤ_{(-)}^♯ ⋙ u⁻¹` and the right adjoint of `u⁻¹ ⋙ ℤ_{(-)}^♯` are the
same functor: both send an abelian sheaf `N` on `(B, K)` to the presheaf of sets
`V ↦ N(u V)`, because `u_*` is restriction along `u.op` and so commutes with the forgetful
functor to presheaves of sets. The two composites differ only by the associativity of functor
composition, which is a definitional equality. -/
def pushforwardForgetAbelianIso :
    u.sheafPushforwardContinuous Ab.{u} J K ⋙
        (sheafToPresheaf J Ab.{u} ⋙ Presheaf.forgetAbelian) ≅
      (sheafToPresheaf K Ab.{u} ⋙ Presheaf.forgetAbelian) ⋙
        (Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type u)).obj u.op :=
  Iso.refl _

/-- **The inverse image commutes with the free abelian sheaf functor**, by uniqueness of left
adjoints: `ℤ_{(-)}^♯ ⋙ u⁻¹ ≅ u⁻¹_{pre} ⋙ ℤ_{(-)}^♯`, where `u⁻¹_{pre}` is the left Kan extension
along `u.op` on presheaves of sets.

The right adjoint of the left-hand side is `u_*` followed by the underlying presheaf of sets
(`CategoryTheory.Presheaf.freeAbelianSheafAdj` composed with
`CategoryTheory.Functor.sheafAdjunctionContinuous`), that of the right-hand side is the underlying
presheaf of sets followed by restriction along `u.op`
(`CategoryTheory.Functor.lanAdjunction` composed with `freeAbelianSheafAdj`), and those agree by
`pushforwardForgetAbelianIso`. -/
@[sga "4 I 5.8.3" "Clause 3, special case"]
def pullbackFreeAbelianSheafIso :
    Presheaf.freeAbelianSheaf J ⋙ u.sheafPullback Ab.{u} J K ≅
      u.op.lan ⋙ Presheaf.freeAbelianSheaf K :=
  Adjunction.leftAdjointUniq
    (((Presheaf.freeAbelianSheafAdj J).comp
      (u.sheafAdjunctionContinuous Ab.{u} J K)).ofNatIsoRight
        (pushforwardForgetAbelianIso u J K))
    ((u.op.lanAdjunction (Type u)).comp (Presheaf.freeAbelianSheafAdj K))

/-- The underlying presheaf of the final sheaf of sets is a final presheaf: `sheafToPresheaf` is a
right adjoint and so preserves the final object. -/
def isTerminal_terminalSheaf_obj :
    IsTerminal ((⊤_ (Sheaf K (Type u))).obj) :=
  terminalIsTerminal.isTerminalObj (sheafToPresheaf K (Type u)) _

/-- The canonical map from the left Kan extension along `u.op` of the final presheaf of `(A, J)`
to the final presheaf of `(B, K)`. -/
def lanTerminalToTerminal :
    u.op.lan.obj ((⊤_ (Sheaf J (Type u))).obj) ⟶ (⊤_ (Sheaf K (Type u))).obj :=
  (isTerminal_terminalSheaf_obj K).from _

end ConstantSheafInverseImage

section LanTerminal

variable {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [PreservesFiniteLimits (u.sheafPullback (Type u) J K)]

/-- The canonical map `lanTerminalToTerminal u J K` becomes an isomorphism after
sheafification, that is, it lies in `K.W`. -/
theorem w_lanTerminalToTerminal : K.W (lanTerminalToTerminal u J K) := by
  rw [GrothendieckTopology.W_iff]
  have hcon : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback u (Type u) J K) :=
    preservesFiniteLimits_of_natIso
      (Functor.sheafPullbackConstruction.sheafPullbackIso u (Type u) J K)
  have h₁ : IsTerminal ((presheafToSheaf K (Type u)).obj
      (u.op.lan.obj ((⊤_ (Sheaf J (Type u))).obj))) :=
    terminalIsTerminal.isTerminalObj
      (Functor.sheafPullbackConstruction.sheafPullback u (Type u) J K) _
  have h₂ : IsTerminal ((presheafToSheaf K (Type u)).obj ((⊤_ (Sheaf K (Type u))).obj)) :=
    IsTerminal.ofIso terminalIsTerminal
      (asIso ((sheafificationAdjunction K (Type u)).counit.app
        (⊤_ (Sheaf K (Type u))))).symm
  rw [h₂.hom_ext ((presheafToSheaf K (Type u)).map (lanTerminalToTerminal u J K))
    (h₁.uniqueUpToIso h₂).hom]
  infer_instance

end LanTerminal

section ConstantSheafInverseImage

variable {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint]
  [(u.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback (Type u) J K)]

/-- **The inverse image of the constant abelian sheaf on `ℤ` is the constant abelian sheaf on
`ℤ`** — the abelian half of [Stacks, Tag 00XO], with no terminal object on either site and no
finality of `u`, only left exactness of the inverse image on sheaves of sets.

The constant sheaf on `ℤ` is the free abelian sheaf on the final sheaf
(`Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf`), the inverse
image commutes with the free abelian sheaf functor (`pullbackFreeAbelianSheafIso`), and the free
abelian sheaf functor does not distinguish the left Kan extension of the final presheaf from the
final presheaf, the canonical map between them being inverted by sheafification
(`w_lanTerminalToTerminal`) and the free abelian sheaf functor inverting such maps
(`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W`).

This is the `e` of `gammaCompPushforwardIsoAbOfConstantSheafIso`. It is not
`Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso`, which proves the same statement for an
arbitrary coefficient category but assumes a terminal object on each site together with an
identification `u(T) ≅ T'`; the argument here is specific to abelian coefficients, the constant
sheaf on `ℤ` being a *free* abelian sheaf. -/
public def pullbackConstantSheafIsoAb :
    (u.sheafPullback Ab.{u} J K).obj
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf K Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  have : IsIso ((Presheaf.freeAbelianSheaf K).map (lanTerminalToTerminal u J K)) :=
    Presheaf.isIso_freeAbelianSheaf_map_of_W K _ (w_lanTerminalToTerminal u J K)
  (u.sheafPullback Ab.{u} J K).mapIso
      (Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf J).symm ≪≫
    (pullbackFreeAbelianSheafIso u J K).app ((⊤_ (Sheaf J (Type u))).obj) ≪≫
    asIso ((Presheaf.freeAbelianSheaf K).map (lanTerminalToTerminal u J K)) ≪≫
    Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf K

end ConstantSheafInverseImage

/-! ### The abelian case, reduced to the inverse image of the constant sheaf on `ℤ` -/

section Abelian

variable {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]

/-- **The abelian global-sections comparison, reduced to one isomorphism of constant sheaves.**
If the inverse image along `u` of the constant abelian sheaf on `ℤ` is the constant abelian sheaf
on `ℤ`, then restriction along `u` does not change the global sections of an abelian sheaf:

`u_* ⋙ Γ(A, -) ≅ Γ(B, -)`.

This is the derivation step of the abelian case, and it is formal. Global sections of abelian
sheaves are corepresented by the constant sheaf on `ℤ`
(`ModuleSheafCohomology.globalSectionsRepresentation`), the adjunction
`u⁻¹ ⊣ u_*` moves `Hom` out of a corepresenting object across as an *additive* equivalence
(`CategoryTheory.Adjunction.homAddEquiv`, available because `u_*` on abelian sheaves preserves
limits and is therefore additive), and `e` identifies the two corepresenting objects. Note that
nothing here touches `CategoryTheory.Sheaf.ΓRes`; the comparison is built in the `Hom` spelling
throughout.

What `e` asks for is the abelian half of [Stacks, Tag 00XO]. It does **not** follow from
`Stacks.ConstantSheaf.gammaCompPushforwardIso`, the set-valued statement of this file: `Sheaf.Γ`
on abelian sheaves is corepresented by the constant sheaf on `ℤ` rather than by a final sheaf, so
left exactness of the inverse image on sheaves of *sets* does not supply it. Nor is it
`Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso`, which proves exactly this for an
arbitrary coefficient category but assumes a terminal object on each site together with an
identification `u(T) ≅ T'` — the hypothesis a site of affine objects over a non-affine scheme
cannot meet. The route to `e` that needs no new Mathlib lemma runs through the free abelian sheaf:
`Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf` identifies the
constant sheaf on `ℤ` with the free abelian sheaf on the final sheaf,
`CategoryTheory.Presheaf.freeAbelianSheafAdj` and `CategoryTheory.Functor.lanAdjunction` identify
`u⁻¹ ∘ ℤ_{(-)}^♯` with `ℤ_{(-)}^♯ ∘ u⁻¹` by uniqueness of left adjoints — their right adjoints
agree because `u_*` is restriction along `u.op` and so commutes with the forgetful functor — and
`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W` then replaces the left Kan extension of
the final presheaf by the final presheaf, the two having the same sheafification by the
set-valued statement of this file. The `J.W` membership that last step needs is
`CategoryTheory.GrothendieckTopology.W_iff`, which reads it as invertibility of the sheafification
of the map; both sheafifications are final sheaves, the one by
`Stacks.ConstantSheaf.isTerminal_constantSheaf_obj` and the other by left exactness of the inverse
image, and any morphism between final objects is an isomorphism. -/
public def gammaCompPushforwardIsoAbOfConstantSheafIso
    (e : (u.sheafPullback Ab.{u} J K).obj
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf K Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) :
    u.sheafPushforwardContinuous Ab.{u} J K ⋙ Sheaf.Γ J Ab.{u} ≅ Sheaf.Γ K Ab.{u} :=
  let _hlim : Limits.PreservesLimitsOfSize.{0, 0}
      (u.sheafPushforwardContinuous Ab.{u} J K) :=
    (u.sheafAdjunctionContinuous Ab.{u} J K).rightAdjoint_preservesLimits
  let _hadd : (u.sheafPushforwardContinuous Ab.{u} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  let _hadd' : (u.sheafPullback Ab.{u} J K).Additive :=
    (u.sheafAdjunctionContinuous Ab.{u} J K).left_adjoint_additive
  Functor.isoWhiskerLeft (u.sheafPushforwardContinuous Ab.{u} J K)
      (ModuleSheafCohomology.globalSectionsRepresentation J) ≪≫
    NatIso.ofComponents
      (fun N => (((u.sheafAdjunctionContinuous Ab.{u} J K).homAddEquiv
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) N).symm).toAddCommGrpIso)
      (by
        intro N N' φ
        ext g
        exact (u.sheafAdjunctionContinuous Ab.{u} J K).homEquiv_naturality_right_symm g φ) ≪≫
    (preadditiveCoyoneda.mapIso e.op).symm ≪≫
    (ModuleSheafCohomology.globalSectionsRepresentation K).symm

end Abelian

/-! ### The abelian comparison, hypothesis-free -/

section AbelianMain

variable {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]
  (u : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B)
  [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint]
  [(u.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback (Type u) J K)]

/-- **Restriction along a morphism of sites does not change global sections, for abelian
sheaves**:

`u_* ⋙ Γ(A, -) ≅ Γ(B, -)` on `Sheaf K Ab`,

with no hypothesis beyond continuity of `u` and left exactness of its inverse image on sheaves of
sets. Neither site needs a terminal object and `u` need not be final.

This is `gammaCompPushforwardIsoAbOfConstantSheafIso` with its one input discharged by
`pullbackConstantSheafIsoAb`. -/
public def gammaCompPushforwardIsoAb :
    u.sheafPushforwardContinuous Ab.{u} J K ⋙ Sheaf.Γ J Ab.{u} ≅ Sheaf.Γ K Ab.{u} :=
  gammaCompPushforwardIsoAbOfConstantSheafIso u J K (pullbackConstantSheafIsoAb u J K)

/-- **Restriction along a morphism of sites does not change global sections, for abelian sheaves**,
in the form a consumer has it: the only hypothesis is
`CategoryTheory.Functor.IsMorphismOfSites`, [Stacks, Tag 00X1].

This is the statement an inverse system of sites needs in order to have a diagram of global
sections at its levels at all: the transition datum of a system of abelian sheaves is a map
`F_j ⟶ (u_a)_* F_k`, so `Sheaf.Γ` of it lands in `Γ_j((u_a)_* F_k)`, and this isomorphism is what
turns that into a map `Γ_j(F_j) ⟶ Γ_k(F_k)`. Every transition of a
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites` carries an `IsMorphismOfSites`,
and so does every functor to the colimit site, by Stacks 0A35. -/
public def gammaCompPushforwardIsoAbOfMorphismOfSites (hu : u.IsMorphismOfSites J K) :
    letI := hu.isContinuous
    u.sheafPushforwardContinuous Ab.{u} J K ⋙ Sheaf.Γ J Ab.{u} ≅ Sheaf.Γ K Ab.{u} :=
  let := hu.isContinuous
  let := hu.preservesFiniteLimits
  gammaCompPushforwardIsoAb u J K

end AbelianMain

end Stacks.ConstantSheaf

end
