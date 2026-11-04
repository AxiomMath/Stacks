module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.InternalHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Differentials
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationGluing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomAction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomTransitivity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationUnthickenedTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocal
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine-local criteria for formal smoothness

[Stacks Project, Tag 0D0F] asserts that four conditions on a morphism of schemes `f : X ⟶ Y` are
equivalent:

1. `f` is formally smooth, `AlgebraicGeometry.FormallySmooth`;
2. every point of `X` has an open neighbourhood `U`, mapping into an open `V` of `Y`, with
   `f|_U : U ⟶ V` formally smooth;
3. for every pair of affine opens `U ⊆ X`, `V ⊆ Y` with `f(U) ⊆ V` the ring map
   `Γ(Y, V) ⟶ Γ(X, U)` is formally smooth;
4. there is an affine open covering `Y = ⋃ V_j` and, for each `j`, an affine open covering
   `f⁻¹(V_j) = ⋃ U_{ji}` with every `Γ(Y, V_j) ⟶ Γ(X, U_{ji})` formally smooth.

The five implications `1 → 2`, `1 → 3`, `2 → 3`, `3 → 4` and `4 → 2` are formal: they are
[Stacks Project, Tag 02H3], the affine criterion [Stacks Project, Tag 02H4] read through
`AlgebraicGeometry.arrowResLEAppIso`, and the affine-locality of formal smoothness of ring maps.
The implication `3 → 1` is the torsor argument of the source, and it is carried out here: given a
first-order thickening `i : T ⟶ T'` of affine schemes and a lifting problem presented by
`a : T ⟶ X` and `h : T' ⟶ Y`, the lifts of `a` over the opens of `T'` form a sheaf of sets which
has a section near every point and is a pseudo-torsor under
`Hom(a^*Ω_{X/Y}, 𝒞_{T/T'})`; the first cohomology of that sheaf of homomorphisms vanishes on the
affine scheme `T`, so the torsor is trivial and has a global section, which is the required lift.

## Main definitions

* `Stacks.Smooth.LiftSet` and `Stacks.Smooth.liftPresheaf`: the lifts of `a : T ⟶ X` over an open
  of `T'` which are morphisms over `Y`, and the presheaf they form on `T'`.
* `Stacks.Smooth.IsLiftPseudoTorsor` is what [Stacks Project, Tag 04FJ] supplies: the sheaf of
  lifts along any first-order thickening is a pseudo-torsor under the sheaf of homomorphisms from
  the pulled-back relative differentials to the conormal sheaf.
* `Stacks.Smooth.liftSetEquivCompatibleLifts`, `Stacks.Smooth.liftHomSectionsEquiv` and
  `Stacks.Smooth.liftAct`: the lifts of a lifting problem over `f` as the compatible lifts of
  [Stacks Project, Tag 04FI], the sections of the sheaf of homomorphisms as the group
  [Stacks Project, Tag 04FJ] acts by, and the resulting action.

## Main results

* `Stacks.Smooth.isSheaf_liftPresheaf`: the lifts of `a` form a sheaf of sets on `T'`.
* `Stacks.Smooth.isLiftPseudoTorsor`: `Stacks.Smooth.IsLiftPseudoTorsor` holds for every
  morphism of schemes, by [Stacks Project, Tag 04FJ].
* `Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_appLE`: [Stacks Project, Tag 06B5]
  with formal smoothness read on sections over pairs of affine opens.
* `Stacks.Smooth.formallySmooth_of_formallySmooth_appLE`: the implication `3 → 1`.
* `Stacks.Smooth.formallySmooth_tfae`: **[Stacks Project, Tag 0D0F]**, all four criteria.

## Implementation notes

The acting sheaf of `Stacks.Smooth.IsLiftPseudoTorsor` is the internal hom
`Hom(a^*Ω_{X/Y}, 𝒞_{T/T'})`, presented by the witness structure `SheafHom` of
[Stacks Project, Tag 01CO], whose sections over an open are identified with the homomorphisms of
the restricted sheaves. Such a witness exists for every pair of sheaves of modules, as
`Stacks.SheafOfModules.internalHomSheafHom`, the internal hom of the ringed site of
[Stacks Project, Tag 03EM].

`Stacks.Smooth.isLiftPseudoTorsor` is [Stacks Project, Tag 04FJ] for the thickening of the
target by the identity, which is the only case the source uses here; Tag 04FJ holds for every
morphism of schemes and mentions neither formal smoothness nor affineness, and so does the
statement here. Both clauses of Tag 04FJ are proved in that generality:
`Stacks.Thickenings.exists_addAction_compatibleLifts` is the action of
`SheafHom(a^*Ω, 𝒞)` on the sheaf of [Stacks Project, Tag 04FI], with both group laws and the
compatibility with the restriction maps of [Stacks Project, Tag 04FH], and
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq` is simple transitivity over an open
carrying a lift. Nothing there is affine and the third condition of Tag 04FI is read on conormal
**sheaves**.

What separates those two clauses from `Stacks.Smooth.IsLiftPseudoTorsor` is not mathematics but
two changes of vocabulary, and the bridge is the `Bridge` section below.

* The lifts. Tag 04FI's lifts are the morphisms `V ⟶ Y'` into a *thickening* `j : Y ⟶ Y'` of the
  target which induce a prescribed map `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{T/T'}` of conormal sheaves, whereas
  a lifting problem over `f` asks for morphisms into `X` itself. Taking `Y = Y' = X` and
  `j = 𝟙 X` makes the two agree: `𝒞_{X/X} = 0`, so the datum `A` carries no information and the
  third condition is vacuous — this is [Stacks Project, Tag 04FK],
  `Stacks.Thickenings.isCompatibleLift_iff_of_isIso` — and the second condition differs from the
  one defining `Stacks.Smooth.LiftSet` only by a composition with the identity. The resulting
  identification is `Stacks.Smooth.liftSetEquivCompatibleLifts`, the identity on underlying
  morphisms, and it carries the restriction maps to each other,
  `Stacks.Smooth.compatibleLiftsRestrict_liftSetEquivCompatibleLifts`.
* The acting group. `Stacks.Thickenings.deformationHomSections` is stated with
  `Stacks.Smooth.cotangentSheaf` and `Stacks.Smooth.IsLiftPseudoTorsor` with
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`; the two are canonically isomorphic by
  `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`, and precomposition with the pullback of that
  isomorphism is `Stacks.Smooth.deformationHomSectionsEquiv`. Composed with the section
  identification of the `SheafHom` witness it is `Stacks.Smooth.liftHomSectionsEquiv`, and both
  halves commute with restriction of sections — the first by
  `Stacks.SheafOfModules.restrictOverHom_comp_left`, the second by the restriction axiom of
  `SheafHom`.

With those two identifications the four properties asked for by
`Stacks.Smooth.IsLiftPseudoTorsor` are the two clauses of Tag 04FJ read across:
`Stacks.Smooth.liftAct` is the action, `Stacks.Smooth.liftAct_zero` and
`Stacks.Smooth.liftAct_add` its group laws, `Stacks.Smooth.liftSetRes_liftAct` its compatibility
with restriction, and `Stacks.Smooth.existsUnique_liftAct_eq` its simple transitivity.

The affine form of the action, `Stacks.Thickenings.existsUnique_act_eq`, is no longer on the
route: there the acting group is the module of `Γ(X, ⊤)`-linear maps
`Ω[Γ(X, ⊤)⁄Γ(Y, ⊤)] ⟶ 𝒞_{T/T'}`, it acts on the lifts defined on all of `T'` rather than on
each open, the third condition of Tag 04FI is read on conormal modules, and both `X` and `Y` are
required to be affine. The last of those is the real restriction — in a lifting problem for `f` the
lift need not land in a single affine chart of `X` lying over an affine open of `Y` — and the
unrestricted sheaf form of Tag 04FJ removes it.

Everything else the argument needs is available. The sheaf of lifts is built from the gluing of
morphisms of schemes along `Stacks.Thickenings.glueCompatibleLifts`; the local sections come from
`Stacks.Smooth.exists_isAffineOpen_lift_of_formallySmooth_appLE`, step (I) of the source's proof;
the classification of torsors by first cohomology is
`Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne` of [Stacks Project, Tag 02FQ],
whose cohomology group is matched with that of a sheaf of modules by
`Stacks.Cohomology.ModuleComparison.underlyingSectionsIso`; and the vanishing of the first
cohomology of the internal hom is
`Stacks.Cohomology.Affine.isZero_firstCohomology_sheafHom_of_isLocallyProjective` of
[Stacks Project, Tag 0D0E], applied to the pullback of `Ω_{X/Y}`, which is locally projective
because `Ω_{X/Y}` is and local projectivity is stable under pullback.

A first-order thickening is a homeomorphism on points, so the sheaf of lifts on `T'` and the sheaf
of homomorphisms on `T` live on homeomorphic spaces; `Stacks.Smooth.nonempty_of_homeomorph_action`
transports the first along the homeomorphism, which keeps the cohomological hypothesis on the
space where it was proved.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
* [Stacks Project, Tag 02H3](https://stacks.math.columbia.edu/tag/02H3)
* [Stacks Project, Tag 02H4](https://stacks.math.columbia.edu/tag/02H4)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 04FK](https://stacks.math.columbia.edu/tag/04FK)
* [Stacks Project, Tag 06B5](https://stacks.math.columbia.edu/tag/06B5)
* [Stacks Project, Tag 0D0E](https://stacks.math.columbia.edu/tag/0D0E)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Smooth

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (i : T ⟶ T') (a : T ⟶ X) (h : T' ⟶ S)

/-- **The lifts of `a` over an open of the thickening.** For a morphism `i : T ⟶ T'`, a morphism
`a : T ⟶ X` and a morphism `h : T' ⟶ S`, this is the set of morphisms `V ⟶ X` over `S` whose
restriction along `i` to `i⁻¹V` is `a`. -/
def LiftSet (V : T'.Opens) : Type u :=
  {b : (V : Scheme.{u}) ⟶ X // b ≫ f = V.ι ≫ h ∧ (i ∣_ V) ≫ b = (i ⁻¹ᵁ V).ι ≫ a}

/-- **Restriction of a lift to a smaller open**, obtained by precomposing with the inclusion;
both conditions defining a lift are stable under shrinking the open. -/
noncomputable def liftSetRes {V W : T'.Opens} (hWV : W ≤ V) :
    LiftSet f i a h V ⟶ LiftSet f i a h W :=
  TypeCat.ofHom fun b => ⟨T'.homOfLE hWV ≫ b.1, by
    rw [Category.assoc, b.2.1, ← Category.assoc, Scheme.homOfLE_ι], by
    rw [← Category.assoc, morphismRestrict_homOfLE i W V hWV, Category.assoc, b.2.2,
      ← Category.assoc, Scheme.homOfLE_ι]⟩

/-- The underlying morphism of a restricted lift is the composite of the inclusion with the
lift. -/
theorem liftSetRes_coe {V W : T'.Opens} (hWV : W ≤ V) (b : LiftSet f i a h V) :
    (liftSetRes f i a h hWV b).1 = T'.homOfLE hWV ≫ b.1 := rfl

/-- **The presheaf of lifts of `a` on `T'`**, the assignment of `Stacks.Smooth.LiftSet` to an
open of `T'` together with its restriction maps. -/
noncomputable def liftPresheaf : TopCat.Presheaf (Type u) T'.carrier where
  obj V := LiftSet f i a h V.unop
  map g := liftSetRes f i a h g.unop.le
  map_id V := by
    ext c
    exact Subtype.ext
      ((congrArg (fun z => z ≫ c.1) (Scheme.homOfLE_rfl T' V.unop)).trans (Category.id_comp c.1))
  map_comp g g' := by
    ext c
    exact Subtype.ext
      ((congrArg (fun z => z ≫ c.1)
        (Scheme.homOfLE_homOfLE T' g'.unop.le g.unop.le).symm).trans (Category.assoc _ _ _))

section Glue

variable {K : Type u} (U : K → T'.Opens) (c : ∀ k, ((U k : T'.Opens) : Scheme.{u}) ⟶ X)
  (hc : ∀ k l, T'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ c k =
    T'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ c l)

/-- A morphism glued from a family of morphisms over `S` is a morphism over `S`. -/
theorem glueCompatibleLifts_comp (h1 : ∀ k, c k ≫ f = (U k).ι ≫ h) :
    Stacks.Thickenings.glueCompatibleLifts U c hc ≫ f = (iSup U).ι ≫ h := by
  refine Stacks.Thickenings.hom_ext_of_opens U (fun k => le_iSup U k)
    (fun _ hx => Opens.mem_iSup.mp hx) _ _ (fun k => ?_)
  rw [← Category.assoc, ← Category.assoc, Stacks.Thickenings.homOfLE_glueCompatibleLifts,
    Scheme.homOfLE_ι, h1 k]

/-- A morphism glued from a family of lifts of `a` is again a lift of `a`. -/
theorem glueCompatibleLifts_morphismRestrict
    (h2 : ∀ k, (i ∣_ U k) ≫ c k = (i ⁻¹ᵁ U k).ι ≫ a) :
    (i ∣_ iSup U) ≫ Stacks.Thickenings.glueCompatibleLifts U c hc =
      (i ⁻¹ᵁ iSup U).ι ≫ a := by
  refine Stacks.Thickenings.hom_ext_of_opens (fun k => i ⁻¹ᵁ U k)
    (fun k => i.preimage_mono (le_iSup U k)) (Stacks.Thickenings.exists_mem_preimage_iSup i U)
    _ _ (fun k => ?_)
  rw [← Category.assoc, ← morphismRestrict_homOfLE i (U k) (iSup U) (le_iSup U k),
    Category.assoc, Stacks.Thickenings.homOfLE_glueCompatibleLifts, h2 k, ← Category.assoc,
    Scheme.homOfLE_ι]

end Glue

/-- The presheaf of lifts of `a` is a sheaf: a morphism of schemes is determined by, and can be
assembled from, its restrictions to an open cover, and both conditions defining a lift are
local. -/
theorem isSheaf_liftPresheaf : (liftPresheaf f i a h).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ (fun K U sf hsf => ?_)
  have hc : ∀ k l, T'.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ (sf k).1 =
      T'.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ (sf l).1 :=
    fun k l => congrArg Subtype.val (hsf k l)
  refine ⟨⟨Stacks.Thickenings.glueCompatibleLifts U (fun k => (sf k).1) hc,
    glueCompatibleLifts_comp f h U _ hc (fun k => (sf k).2.1),
    glueCompatibleLifts_morphismRestrict i a U _ hc (fun k => (sf k).2.2)⟩,
    fun k => ?_, fun s hs => ?_⟩
  · exact Subtype.ext
      (Stacks.Thickenings.homOfLE_glueCompatibleLifts U (fun k => (sf k).1) hc k)
  · refine Subtype.ext (Stacks.Thickenings.hom_ext_of_opens U (fun k => le_iSup U k)
      (fun _ hx => Opens.mem_iSup.mp hx) _ _ (fun k => ?_))
    exact (congrArg Subtype.val (hs k)).trans
      (Stacks.Thickenings.homOfLE_glueCompatibleLifts U (fun k => (sf k).1) hc k).symm

/-- **Local projectivity of the sheaf of relative differentials from the affine-local
criterion.** This is [Stacks Project, Tag 06B5] with formal smoothness read on sections over
pairs of affine opens instead of as the lifting property of the morphism. -/
@[ega "IV 16.10.2" "Condition (i)", ega "IV 17.2.3"]
theorem isLocallyProjective_relativeDifferentials_of_appLE {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ U : X.Opens, IsAffineOpen U → ∀ V : S.Opens, IsAffineOpen V →
      ∀ hUV : U ≤ f ⁻¹ᵁ V, (f.appLE V U hUV).hom.FormallySmooth) :
    Scheme.Modules.IsLocallyProjective (Scheme.Hom.relativeDifferentials f) := by
  rw [AlgebraicGeometry.isLocallyProjective_iff_exists_affineOpen_cover]
  refine ⟨Σ V : S.affineOpens, {U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)},
    fun j => (j.2.1 : X.Opens), TopologicalSpace.IsOpenCover.mk ?_, fun j => j.2.1.2, ?_⟩
  · rw [iSup_sigma]
    exact Eq.trans
      (iSup_congr fun V : S.affineOpens => iSup_affineOpens_le_eq X (f ⁻¹ᵁ (V : S.Opens)))
      (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  · rintro ⟨V, U, hUV⟩
    show Module.Projective Γ(X, (U : X.Opens))
      Γ(Scheme.Hom.relativeDifferentials f, (U : X.Opens))
    have _ : IsAffine (U : X.Opens) := U.2
    have _ : IsAffine (V : S.Opens) := V.2
    let _ : Algebra Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) :=
      (f.appLE (V : S.Opens) (U : X.Opens) hUV).hom.toAlgebra
    have : Algebra.FormallySmooth Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) := by
      rw [← RingHom.formallySmooth_algebraMap]
      exact hf _ U.2 _ V.2 hUV
    obtain ⟨e, -⟩ :=
      Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
        f U.2 hUV V.2
    have eL : Ω[Γ(X, (U : X.Opens))⁄Γ(S, (V : S.Opens))] ≃ₗ[Γ(X, (U : X.Opens))]
        Γ(Scheme.Hom.relativeDifferentials f, (U : X.Opens)) := e.symm.toLinearEquiv
    exact Module.Projective.of_equiv' eL

/-! ### Torsors under an abelian sheaf, and the vanishing of their class -/

section Torsor

open Stacks.Cohomology.SheafTorsor

/-- A sheaf of types on a space, read as a sheaf of sets in the sense of
[Stacks Project, Tag 02FO]. -/
private def sheafOfSets {Z : TopCat.{u}} (F : TopCat.Sheaf (Type u) Z) :
    Stacks.SpaceTorsor.SheafOfSets Z where
  obj V := F.obj.obj (.op V)
  res hle := F.obj.map (homOfLE hle).op
  res_self V s := by simp
  res_comp h₁ h₂ s := by
    change (F.obj.map _ ≫ F.obj.map _) s = _
    rw [← F.obj.map_comp]
    rfl
  isSheaf := by
    intro V I W hW hcover
    refine ⟨fun s t hst => F.eq_of_locally_eq' W V (fun k => homOfLE (hW k)) hcover.le _ _
      fun k => congrArg (fun z => z.val k) hst, fun s => ?_⟩
    obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W V (fun k => homOfLE (hW k)) hcover.le s.val
      (fun k l => s.property k l (W k ⊓ W l) inf_le_left inf_le_right)
    exact ⟨t, Subtype.ext (funext ht)⟩

/-- An abelian sheaf as a torsor under itself, the trivial torsor. -/
private def trivialTorsor {Z : TopCat.{u}} (H : TopCat.Sheaf AddCommGrpCat.{u} Z) :
    Torsor Z H where
  F :=
    { obj := fun V => H.obj.obj (.op V)
      res := fun hle => H.obj.map (homOfLE hle).op
      res_self := by simp
      res_comp := by
        intros
        rw [← ConcreteCategory.comp_apply, ← H.obj.map_comp]
        rfl
      isSheaf := (sheafOfSets
        ((sheafCompose _ (forget AddCommGrpCat.{u})).obj H)).isSheaf }
  action :=
    { act := fun {V} g s => (show H.obj.obj (.op V) from g) + s
      one_act := by intros; exact zero_add _
      mul_act := by intros; exact add_assoc _ _ _
      res_act := by
        intro V W hle g s
        exact map_add (H.obj.map (homOfLE hle).op).hom _ _ }
  isTorsor := by
    refine ⟨fun V hV => ⟨hV, fun s t => ⟨Multiplicative.ofAdd (t - s), ?_, ?_⟩⟩,
      fun x => ⟨⊤, trivial, ⟨0⟩⟩⟩
    · exact sub_add_cancel t s
    · intro g hg
      change (show H.obj.obj (.op V) from g) + s = t at hg
      change (show H.obj.obj (.op V) from g) = t - s
      exact eq_sub_of_add_eq hg

/-- Isomorphic torsors have global sections together. -/
private theorem torsor_nonempty_of_class_eq {Z : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{u} Z} {F G : Torsor Z H}
    (hFG : (Quotient.mk _ F : TorsorClass Z H) = Quotient.mk _ G) :
    Nonempty (F.F.obj ⊤) ↔ Nonempty (G.F.obj ⊤) := by
  have hrel := Quotient.exact hFG
  clear hFG
  induction hrel with
  | rel F G hr =>
    obtain ⟨φ, hφ⟩ := hr
    exact ⟨fun ⟨s⟩ => ⟨φ.app ⊤ s⟩, fun ⟨t⟩ => ⟨(hφ ⊤).surjective t |>.choose⟩⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A torsor under an abelian sheaf with vanishing first cohomology has a global section.**
Its class in the first cohomology group agrees with that of the trivial torsor, which has
one. -/
private theorem torsor_nonempty_of_isZero {Z : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
    {H : TopCat.Sheaf AddCommGrpCat.{u} Z} (F : Torsor Z H)
    (hH : IsZero (sheafCohomologyOne Z H)) :
    Nonempty (F.F.obj ⊤) := by
  have heq : (Quotient.mk _ F : TorsorClass Z H) = Quotient.mk _ (trivialTorsor H) :=
    (torsorClassEquivSheafCohomologyOne Z H).injective
      ((AddCommGrpCat.isZero_iff_subsingleton.mp hH).elim _ _)
  exact (torsor_nonempty_of_class_eq heq).mpr ⟨(0 : H.obj.obj (.op ⊤))⟩

/-- **A sheaf of sets on a space homeomorphic to `Z`, acted on simply transitively by an abelian
sheaf on `Z` with vanishing first cohomology and having sections near every point, has a global
section.** The action is transported along the homeomorphism and the resulting torsor is
trivialized by `Stacks.Smooth.torsor_nonempty_of_isZero`. -/
private theorem nonempty_of_homeomorph_action {Z W : TopCat.{u}} (e : Z ≅ W)
    (H : TopCat.Sheaf AddCommGrpCat.{u} Z) (F : TopCat.Sheaf (Type u) W)
    (act : ∀ V : Opens W,
      H.obj.obj (.op ((Opens.map e.hom).obj V)) → F.obj.obj (.op V) → F.obj.obj (.op V))
    (hzero : ∀ V s, act V 0 s = s)
    (hadd : ∀ V g g' s, act V (g + g') s = act V g (act V g' s))
    (hres : ∀ (V W' : Opens W) (hle : W' ≤ V) g s,
      F.obj.map (homOfLE hle).op (act V g s) =
        act W' (H.obj.map ((Opens.map e.hom).map (homOfLE hle)).op g)
          (F.obj.map (homOfLE hle).op s))
    (hunique : ∀ V s t, ∃! g, act V g s = t)
    (hne : ∀ y : W, ∃ V : Opens W, y ∈ V ∧ Nonempty (F.obj.obj (.op V)))
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
    (hH : IsZero (sheafCohomologyOne Z H)) :
    Nonempty (F.obj.obj (.op ⊤)) := by
  let E := Opens.mapMapIso e
  let FG := (TopCat.Sheaf.pushforward (Type u) e.inv).obj F
  let q (V : Opens Z) := H.obj.mapIso (E.counitIso.app V).op
  let A : Stacks.SpaceTorsor.Action (underlyingPresheafOfGroups Z H)
      (sheafOfSets FG).toPresheafOfSets :=
    { act := fun {V} g s => act (E.inverse.obj V) ((q V).hom g.toAdd) s
      one_act := by
        intro V s
        show act _ ((q V).hom 0) s = s
        rw [map_zero]
        exact hzero _ _
      mul_act := by
        intro V g g' s
        show act _ ((q V).hom
          ((show H.obj.obj (.op V) from g) + (show H.obj.obj (.op V) from g'))) s = _
        rw [map_add]
        exact hadd _ _ _ _
      res_act := by
        intro V W' hle g s
        have hmap : (q V).hom ≫
              H.obj.map ((Opens.map e.hom).map (E.inverse.map (homOfLE hle))).op =
            H.obj.map (homOfLE hle).op ≫ (q W').hom := by
          simp only [q, Functor.mapIso_hom, ← Functor.map_comp]
          exact (H.obj.map_comp _ _).symm.trans
            (congrArg H.obj.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
        have hel := ConcreteCategory.congr_hom hmap (Multiplicative.toAdd g)
        simp only [ConcreteCategory.comp_apply] at hel
        have hr := hres (E.inverse.obj V) (E.inverse.obj W')
          (E.inverse.map (homOfLE hle)).le ((q V).hom (Multiplicative.toAdd g)) s
        rw [show homOfLE (E.inverse.map (homOfLE hle)).le =
          E.inverse.map (homOfLE hle) from Subsingleton.elim _ _] at hr
        show F.obj.map ((E.inverse.map (homOfLE hle)).op)
            (act _ ((q V).hom (Multiplicative.toAdd g)) s) = _
        rw [hr]
        congr 1 }
  have hA : A.IsTorsor := by
    refine ⟨fun V hV => ⟨hV, fun s t => ?_⟩, fun x => ?_⟩
    · obtain ⟨g, hg, hgu⟩ := hunique (E.inverse.obj V) s t
      refine ⟨Multiplicative.ofAdd ((q V).inv g), ?_, fun g' hg' => ?_⟩
      · show act _ ((q V).hom ((q V).inv g)) s = t
        rw [(q V).inv_hom_id_apply g]
        exact hg
      · apply Multiplicative.toAdd.injective
        apply (ConcreteCategory.bijective_of_isIso (q V).hom).injective
        show (q V).hom (Multiplicative.toAdd g') = (q V).hom ((q V).inv g)
        rw [(q V).inv_hom_id_apply g]
        exact hgu ((q V).hom (Multiplicative.toAdd g')) hg'
    · obtain ⟨V, hx, ⟨s⟩⟩ := hne (e.hom x)
      exact ⟨E.functor.obj V, hx, ⟨F.obj.map (E.unitIso.app V).inv.op s⟩⟩
  obtain ⟨s⟩ := torsor_nonempty_of_isZero ⟨sheafOfSets FG, A, hA⟩ hH
  exact ⟨F.obj.map (homOfLE (show (⊤ : Opens W) ≤ E.inverse.obj ⊤ from
    fun _ _ => trivial)).op s⟩

end Torsor

/-! ### Tag 04FJ for a lifting problem over `f` -/

section PseudoTorsor

/-- **[Stacks Project, Tag 04FJ] for a lifting problem over `f`.** For every first-order
thickening `i : T ⟶ T'` and every lifting problem presented by `a : T ⟶ X`, `h : T' ⟶ S`, the
sheaf of lifts of `a` on `T'` is a pseudo-torsor under the sheaf of homomorphisms
`a^*Ω_{X/S} ⟶ 𝒞_{T/T'}`: that sheaf acts on the lifts over every open, compatibly with
restriction, and the action is simply transitive wherever a lift exists. -/
def IsLiftPseudoTorsor {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ {T T' : Scheme.{u}} {i : T ⟶ T'} [IsClosedImmersion i],
    Stacks.Thickenings.IsFirstOrderThickening i → ∀ (a : T ⟶ X) (h : T' ⟶ S), a ≫ f = i ≫ h →
      ∃ (H : SheafHom T.sheaf
            ((Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials f))
            (Stacks.Conormal.conormalSheaf i))
        (act : ∀ V : T'.Opens, Γ(H.obj, i ⁻¹ᵁ V) → LiftSet f i a h V → LiftSet f i a h V),
        (∀ V s, act V 0 s = s) ∧
        (∀ V θ η s, act V (θ + η) s = act V θ (act V η s)) ∧
        (∀ (V W : T'.Opens) (hWV : W ≤ V) θ s,
          liftSetRes f i a h hWV (act V θ s) =
            act W (H.obj.val.map (homOfLE (i.preimage_mono hWV)).op θ)
              (liftSetRes f i a h hWV s)) ∧
        (∀ V s t, ∃! θ, act V θ s = t)

/-- **`a^*Ω_{X/S}` in the two spellings of the sheaf of relative differentials.** The pullback
along `a : T ⟶ X` of the comparison isomorphism
`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` between
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, which
`Stacks.Smooth.IsLiftPseudoTorsor` and [Stacks Project, Tag 06B5] are stated with, and
`Stacks.Smooth.cotangentSheaf`, which [Stacks Project, Tag 04FJ] acts through. Precomposition
with it on *global* morphisms out of `a^*Ω_{X/S}` is
`Stacks.Thickenings.derivationDatumEquiv`; what the torsor needs is its effect on the sections
of the sheaf of homomorphisms over an open, which is
`Stacks.Smooth.deformationHomSectionsEquiv`. -/
noncomputable def pullbackRelativeDifferentialsIso {X S T : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ X) :
    (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials f) ≅
      pullbackCotangentSheaf f a :=
  (Scheme.Modules.pullback a).mapIso (Scheme.Hom.cotangentSheafIso f)

section Bridge

variable {X S T T' : Scheme.{u}} {f : X ⟶ S} {i : T ⟶ T'} [IsClosedImmersion i] {a : T ⟶ X}
  {h : T' ⟶ S}

/-- **The acting group of [Stacks Project, Tag 04FJ], in the spelling of
`Stacks.Smooth.IsLiftPseudoTorsor`.** Over the part `i⁻¹V` of `T` cut out by an open `V` of `T'`,
precomposition with `Stacks.Smooth.pullbackRelativeDifferentialsIso` identifies the maps
`a^*Ω_{X/S}|_{i⁻¹V} ⟶ 𝒞_{T/T'}|_{i⁻¹V}` read on
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` with
`Stacks.Thickenings.deformationHomSections`, the group that Tag 04FJ acts by.

The structure morphism of the target appears as `𝟙 X ≫ f`: Tag 04FJ is applied here with the
*identity* thickening `𝟙 X` of `X`, whose composite with the structure morphism `f` of `X` over
`S` is the one Tag 04FJ reads the differentials of. -/
noncomputable def deformationHomSectionsEquiv (V : T'.Opens) :
    Stacks.Thickenings.moduleHomSections
        ((Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials f))
        (Stacks.Thickenings.conormalModules i) (i ⁻¹ᵁ V) ≃+
      Stacks.Thickenings.deformationHomSections i a (𝟙 X ≫ f) V where
  toFun θ := (pullbackRelativeDifferentialsIso f a).inv.over (i ⁻¹ᵁ V) ≫ θ
  invFun φ := (pullbackRelativeDifferentialsIso f a).hom.over (i ⁻¹ᵁ V) ≫ φ
  left_inv θ := Iso.map_hom_inv_id_assoc (pullbackRelativeDifferentialsIso f a) _ θ
  right_inv φ := Iso.map_inv_hom_id_assoc (pullbackRelativeDifferentialsIso f a) _ φ
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

/-- **`Stacks.Smooth.deformationHomSectionsEquiv` commutes with restriction of sections**:
precomposition with a fixed map is natural in the open, which is
`Stacks.SheafOfModules.restrictOverHom_comp_left`. -/
theorem deformationHomSectionsEquiv_restrict {V W : T'.Opens} (hWV : W ≤ V)
    (θ : Stacks.Thickenings.moduleHomSections
        ((Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials f))
        (Stacks.Thickenings.conormalModules i) (i ⁻¹ᵁ V)) :
    deformationHomSectionsEquiv (f := f) (a := a) W
        (Stacks.Thickenings.moduleHomSections.restrict (i.preimage_mono hWV) θ)
      = Stacks.Thickenings.moduleHomSections.restrict (i.preimage_mono hWV)
          (deformationHomSectionsEquiv V θ) :=
  (Stacks.SheafOfModules.restrictOverHom_comp_left _ _ (i.preimage_mono hWV)
    (pullbackRelativeDifferentialsIso f a).inv θ).symm

variable (H : SheafHom T.sheaf
    ((Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials f))
    (Stacks.Conormal.conormalSheaf i))

/-- **A section of `SheafHom(a^*Ω_{X/S}, 𝒞_{T/T'})` over `i⁻¹V` as an element of the group of
[Stacks Project, Tag 04FJ].** The identification of sections carried by the witness structure
`SheafHom` of [Stacks Project, Tag 01CO], followed by
`Stacks.Smooth.deformationHomSectionsEquiv`. -/
noncomputable def liftHomSectionsEquiv (V : T'.Opens) :
    Γ(H.obj, i ⁻¹ᵁ V) ≃+ Stacks.Thickenings.deformationHomSections i a (𝟙 X ≫ f) V :=
  (H.sectionsEquiv (i ⁻¹ᵁ V)).trans (deformationHomSectionsEquiv (f := f) (a := a) V)

/-- **`Stacks.Smooth.liftHomSectionsEquiv` commutes with restriction of sections.** Both halves
do: the restriction axiom of `SheafHom` is `SheafHom.sectionsEquiv_restrict` and the other half
is `Stacks.Smooth.deformationHomSectionsEquiv_restrict`. -/
theorem liftHomSectionsEquiv_restrict {V W : T'.Opens} (hWV : W ≤ V) (σ : Γ(H.obj, i ⁻¹ᵁ V)) :
    liftHomSectionsEquiv H W (H.obj.val.map (homOfLE (i.preimage_mono hWV)).op σ)
      = Stacks.Thickenings.moduleHomSections.restrict (i.preimage_mono hWV)
          (liftHomSectionsEquiv H V σ) :=
  (congrArg (deformationHomSectionsEquiv (f := f) (a := a) W)
      (SheafHom.sectionsEquiv_restrict H (i.preimage_mono hWV) σ)).trans
    (deformationHomSectionsEquiv_restrict hWV (H.sectionsEquiv (i ⁻¹ᵁ V) σ))

variable (A : (RingedSpaceModuleAdjunction.modulePullback a.toLRSHom.toShHom).obj
    (Stacks.Thickenings.immersionConormalSheaf (𝟙 X)) ⟶
      Stacks.Thickenings.immersionConormalSheaf i)

/-- **The lifts of a lifting problem over `f` are the compatible lifts of
[Stacks Project, Tag 04FI] for the identity thickening of the target.** A lift of `a : T ⟶ X`
over an open `V` of `T'` is a morphism `V ⟶ X` over `S` restricting to `a` on `i⁻¹V`; a
compatible lift for the thickening `𝟙 X` of `X` and a conormal datum `A` is a morphism
`V ⟶ X` over `S` restricting to `a ≫ 𝟙 X` on `i⁻¹V` and inducing `A|_{i⁻¹V}` on conormal
sheaves. The third condition is vacuous because `𝒞_{X/X} = 0`
(`Stacks.Thickenings.isCompatibleLift_iff_of_isIso`, the content of
[Stacks Project, Tag 04FK]), and the second differs only by the identity, so the two sets are
the same morphisms. -/
def liftSetEquivCompatibleLifts (V : T'.Opens) :
    LiftSet f i a h V ≃ Stacks.Thickenings.compatibleLifts h f a A V where
  toFun b := ⟨b.1, (Stacks.Thickenings.isCompatibleLift_iff_of_isIso h f a A V b.1).mpr
    ⟨b.2.1, b.2.2.trans (Category.comp_id _).symm⟩⟩
  invFun c := ⟨c.1, c.2.1,
    (((Stacks.Thickenings.isCompatibleLift_iff_of_isIso h f a A V c.1).mp c.2).2).trans
      (Category.comp_id _)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- **`Stacks.Smooth.liftSetEquivCompatibleLifts` is compatible with the restriction maps.** Both
restrictions compose the lift with the inclusion of opens, so the identification is the identity
on underlying morphisms on both sides. -/
theorem compatibleLiftsRestrict_liftSetEquivCompatibleLifts {V W : T'.Opens} (hWV : W ≤ V)
    (b : LiftSet f i a h V) :
    Stacks.Thickenings.compatibleLiftsRestrict h f a A hWV (liftSetEquivCompatibleLifts A V b)
      = liftSetEquivCompatibleLifts A W (liftSetRes f i a h hWV b) :=
  Subtype.ext rfl

variable (hsq : i.ker ^ 2 = ⊥)

/-- **The action of a section of `SheafHom(a^*Ω_{X/S}, 𝒞_{T/T'})` on the lifts of `a` over an
open.** The action `Stacks.Thickenings.compatibleLiftsVAdd` of [Stacks Project, Tag 04FJ], read
through the two identifications `Stacks.Smooth.liftHomSectionsEquiv` and
`Stacks.Smooth.liftSetEquivCompatibleLifts`. -/
noncomputable def liftAct (V : T'.Opens) (σ : Γ(H.obj, i ⁻¹ᵁ V)) (b : LiftSet f i a h V) :
    LiftSet f i a h V :=
  (liftSetEquivCompatibleLifts A V).symm
    (Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A V (liftHomSectionsEquiv H V σ)
      (liftSetEquivCompatibleLifts (h := h) A V b))

/-- `Stacks.Smooth.liftAct` read as a compatible lift of [Stacks Project, Tag 04FI]. -/
theorem liftSetEquivCompatibleLifts_liftAct (V : T'.Opens) (σ : Γ(H.obj, i ⁻¹ᵁ V))
    (b : LiftSet f i a h V) :
    liftSetEquivCompatibleLifts A V (liftAct H A hsq V σ b)
      = Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A V (liftHomSectionsEquiv H V σ)
          (liftSetEquivCompatibleLifts A V b) :=
  (liftSetEquivCompatibleLifts A V).apply_symm_apply _

/-- **The zero section acts trivially**, `Stacks.Thickenings.homSectionAct_zero`. -/
theorem liftAct_zero (V : T'.Opens) (b : LiftSet f i a h V) :
    liftAct H A hsq V 0 b = b :=
  (liftSetEquivCompatibleLifts A V).injective
    ((liftSetEquivCompatibleLifts_liftAct H A hsq V 0 b).trans
      ((congrArg (fun z => Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A V z
            (liftSetEquivCompatibleLifts A V b)) (map_zero (liftHomSectionsEquiv H V))).trans
        (Subtype.ext Stacks.Thickenings.homSectionAct_zero)))

/-- **A sum acts as the composite of the two actions**,
`Stacks.Thickenings.homSectionAct_add`. -/
theorem liftAct_add (V : T'.Opens) (σ τ : Γ(H.obj, i ⁻¹ᵁ V)) (b : LiftSet f i a h V) :
    liftAct H A hsq V (σ + τ) b = liftAct H A hsq V σ (liftAct H A hsq V τ b) := by
  refine (liftSetEquivCompatibleLifts A V).injective ?_
  refine (liftSetEquivCompatibleLifts_liftAct H A hsq V (σ + τ) b).trans ?_
  refine Eq.trans ?_ (liftSetEquivCompatibleLifts_liftAct H A hsq V σ
    (liftAct H A hsq V τ b)).symm
  refine Eq.trans ?_ (congrArg
    (Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A V (liftHomSectionsEquiv H V σ))
    (liftSetEquivCompatibleLifts_liftAct H A hsq V τ b).symm)
  refine Eq.trans (congrArg (fun z => Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A V z
    (liftSetEquivCompatibleLifts A V b)) (map_add (liftHomSectionsEquiv H V) σ τ)) ?_
  exact Subtype.ext Stacks.Thickenings.homSectionAct_add

/-- **The action commutes with restriction to a smaller open**, which is the sheaf-action clause
of [Stacks Project, Tag 04FJ],
`Stacks.Thickenings.compatibleLiftsRestrict_compatibleLiftsVAdd`, together with the two
identifications restricting. -/
theorem liftSetRes_liftAct {V W : T'.Opens} (hWV : W ≤ V) (σ : Γ(H.obj, i ⁻¹ᵁ V))
    (b : LiftSet f i a h V) :
    liftSetRes f i a h hWV (liftAct H A hsq V σ b)
      = liftAct H A hsq W (H.obj.val.map (homOfLE (i.preimage_mono hWV)).op σ)
          (liftSetRes f i a h hWV b) :=
  (liftSetEquivCompatibleLifts A W).injective
    ((compatibleLiftsRestrict_liftSetEquivCompatibleLifts A hWV _).symm.trans
      (((congrArg (Stacks.Thickenings.compatibleLiftsRestrict h f a A hWV)
            (liftSetEquivCompatibleLifts_liftAct H A hsq V σ b)).trans
          ((Stacks.Thickenings.compatibleLiftsRestrict_compatibleLiftsVAdd hsq h f a A hWV _
              _).trans
            (congrArg
              (fun c => Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A W
                (Stacks.Thickenings.moduleHomSections.restrict (i.preimage_mono hWV)
                  (liftHomSectionsEquiv H V σ)) c)
              (compatibleLiftsRestrict_liftSetEquivCompatibleLifts A hWV b)))).trans
        (((congrArg (fun z => Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A W z
              (liftSetEquivCompatibleLifts A W (liftSetRes f i a h hWV b)))
            (liftHomSectionsEquiv_restrict H hWV σ)).symm).trans
          (liftSetEquivCompatibleLifts_liftAct H A hsq W _ _).symm)))

/-- **The action is simply transitive on the lifts over an open**: this is the transitivity
clause of [Stacks Project, Tag 04FJ],
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`, read through the two
identifications. -/
theorem existsUnique_liftAct_eq (V : T'.Opens) (b c : LiftSet f i a h V) :
    ∃! σ : Γ(H.obj, i ⁻¹ᵁ V), liftAct H A hsq V σ b = c := by
  obtain ⟨θ, hθ, huniq⟩ := Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq hsq h f a A V
    (liftSetEquivCompatibleLifts (h := h) A V b) (liftSetEquivCompatibleLifts (h := h) A V c)
  refine ⟨(liftHomSectionsEquiv H V).symm θ, (liftSetEquivCompatibleLifts A V).injective ?_,
    fun σ hσ => (liftHomSectionsEquiv H V).injective ?_⟩
  · refine (liftSetEquivCompatibleLifts_liftAct H A hsq V _ b).trans (Eq.trans ?_ hθ)
    exact congrArg (fun z => Stacks.Thickenings.compatibleLiftsVAdd hsq h f a A V z
      (liftSetEquivCompatibleLifts A V b)) ((liftHomSectionsEquiv H V).apply_symm_apply θ)
  · refine Eq.trans (huniq (liftHomSectionsEquiv H V σ) ?_)
      ((liftHomSectionsEquiv H V).apply_symm_apply θ).symm
    exact (liftSetEquivCompatibleLifts_liftAct H A hsq V σ b).symm.trans
      (congrArg (liftSetEquivCompatibleLifts A V) hσ)

end Bridge

/-- **`Stacks.Smooth.IsLiftPseudoTorsor` holds for every morphism of schemes.** This is
[Stacks Project, Tag 04FJ] specialised to the *identity* thickening `𝟙 X` of the target: the
lifting problems of a morphism `f : X ⟶ S` ask for morphisms into `X` itself rather than into a
thickening of `X`, so the conormal datum `A : a^*𝒞_{X/X} ⟶ 𝒞_{T/T'}` of
[Stacks Project, Tag 04FH] carries no information and the third condition of
[Stacks Project, Tag 04FI] is vacuous. Under that specialisation the set
`Stacks.Smooth.LiftSet` of lifts of `a` over an open is
`Stacks.Thickenings.compatibleLifts`, by `Stacks.Smooth.liftSetEquivCompatibleLifts`, and the
sections of `SheafHom(a^*Ω_{X/S}, 𝒞_{T/T'})` are the group Tag 04FJ acts by, by
`Stacks.Smooth.liftHomSectionsEquiv`.

The two clauses of Tag 04FJ then give the four properties: the action with its group laws and
its compatibility with restriction is
`Stacks.Thickenings.exists_addAction_compatibleLifts`, whose action is
`Stacks.Thickenings.compatibleLiftsVAdd`, and simple transitivity over an open carrying a lift
is `Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`. Neither assumes anything affine,
and the third condition of Tag 04FI is read on conormal **sheaves** there, so no restriction
survives into the statement here.

The sheaf of homomorphisms itself is the internal hom of the ringed site,
`Stacks.SheafOfModules.internalHomSheafHom`, which exists for every pair of sheaves of
modules. -/
@[ega "IV 16.5.17", sga "1 III 5.1", sga "1 III 5.4" "more general", sga "3 XII 9.4" "For each T"]
theorem isLiftPseudoTorsor {X S : Scheme.{u}} (f : X ⟶ S) : IsLiftPseudoTorsor f := by
  intro T T' i _ hi a h _
  exact ⟨Stacks.SheafOfModules.internalHomSheafHom T.sheaf _ _,
    liftAct _ 0 hi.2, liftAct_zero _ 0 hi.2, liftAct_add _ 0 hi.2,
    fun V W hWV => liftSetRes_liftAct _ 0 hi.2 hWV, existsUnique_liftAct_eq _ 0 hi.2⟩

end PseudoTorsor

/-! ### The local-to-global step -/

section Assembly

/-- **The implication (3) ⟹ (1) of [Stacks Project, Tag 0D0F].** A morphism of schemes inducing
a formally smooth ring map on sections over every compatible pair of affine opens has the
infinitesimal lifting property.

Fix a first-order thickening `i : T ⟶ T'` of affine schemes and a lifting problem presented by
`a : T ⟶ X` and `h : T' ⟶ S`. The lifts of `a` over the opens of `T'` form a sheaf,
`Stacks.Smooth.isSheaf_liftPresheaf`, which has a section near every point of `T'` by
[Stacks Project, Tag 02H3] and the affine criterion, and which is a pseudo-torsor under
`Hom(a^*Ω_{X/S}, 𝒞_{T/T'})` by [Stacks Project, Tag 04FJ],
`Stacks.Smooth.isLiftPseudoTorsor`. That sheaf of homomorphisms has
vanishing first cohomology on the affine scheme `T` by [Stacks Project, Tag 0D0E], because
`Ω_{X/S}` is locally projective by [Stacks Project, Tag 06B5] and local projectivity is stable
under pullback; so the torsor is trivial and has a global section, which is the required
lift. -/
@[sga "1 III 5.2" "special case", sga "3 IX 3.3" "special case", sga "3 XV 1.1" "more general"]
theorem formallySmooth_of_formallySmooth_appLE {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ U : X.Opens, IsAffineOpen U → ∀ V : S.Opens, IsAffineOpen V →
      ∀ hUV : U ≤ f ⁻¹ᵁ V, (f.appLE V U hUV).hom.FormallySmooth) :
    AlgebraicGeometry.FormallySmooth f := by
  intro T T' hTa hT'a i hi a h hcomm
  have _ : IsAffine T := hTa
  have _ : IsAffine T' := hT'a
  have _ : IsClosedImmersion i := hi.1
  have _ : IsIso i.base := TopCat.isIso_of_bijective_of_isClosedMap i.base
    ⟨i.isClosedEmbedding.injective, hi.isThickening.2⟩ i.isClosedEmbedding.isClosedMap
  obtain ⟨H, act, hzero, hadd, hres, huniq⟩ := isLiftPseudoTorsor f hi a h hcomm
  have hqcΩ : (Scheme.Hom.relativeDifferentials f).IsQuasicoherent := inferInstance
  have hqc := @SheafOfModules.modulePullback_isQuasicoherent _ _ a.toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentials f) hqcΩ
  have hcqc := Stacks.Conormal.conormalSheaf_isQuasicoherent i
  have hproj : Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials f)) :=
    pullback_isLocallyProjective a _ (isLocallyProjective_relativeDifferentials_of_appLE f hf)
  have hH0 := @Stacks.Cohomology.Affine.isZero_firstCohomology_sheafHom_of_isLocallyProjective
    T hTa _ (Stacks.Conormal.conormalSheaf i) hqc hcqc H hproj
  have hH1 : IsZero (Stacks.Cohomology.SheafTorsor.sheafCohomologyOne T.carrier
      ((SheafOfModules.toSheaf T.ringCatSheaf).obj H.obj)) :=
    hH0.of_iso
      ((Stacks.Cohomology.ModuleComparison.underlyingSectionsIso T.ringCatSheaf ⊤ 1).app
        H.obj).symm
  have hne : ∀ t : T', ∃ V : T'.Opens, t ∈ V ∧ Nonempty (LiftSet f i a h V) := by
    intro t
    obtain ⟨V, -, htV, b, hb₁, hb₂⟩ :=
      exists_isAffineOpen_lift_of_formallySmooth_appLE f hf hi a h hcomm t
    exact ⟨V, htV, ⟨b, hb₁, hb₂⟩⟩
  obtain ⟨b⟩ := nonempty_of_homeomorph_action (asIso i.base)
    ((SheafOfModules.toSheaf T.ringCatSheaf).obj H.obj)
    ⟨liftPresheaf f i a h, isSheaf_liftPresheaf f i a h⟩ act hzero hadd hres huniq hne hH1
  refine ⟨T'.topIso.inv ≫ b.1, ?_, ?_⟩
  · rw [Category.assoc, b.2.1, ← Category.assoc,
      show T'.topIso.inv ≫ (⊤ : T'.Opens).ι = 𝟙 T' from T'.topIso.inv_hom_id, Category.id_comp]
  · have _ : IsIso (i ⁻¹ᵁ (⊤ : T'.Opens)).ι := by
      rw [i.preimage_top]
      exact T.topIso.isIso_hom
    refine (cancel_epi (i ⁻¹ᵁ (⊤ : T'.Opens)).ι).mp ?_
    calc (i ⁻¹ᵁ (⊤ : T'.Opens)).ι ≫ i ≫ T'.topIso.inv ≫ b.1
        = (i ∣_ (⊤ : T'.Opens)) ≫ ((⊤ : T'.Opens).ι ≫ T'.topIso.inv) ≫ b.1 := by
          rw [← Category.assoc, ← morphismRestrict_ι]
          simp only [Category.assoc]
      _ = (i ∣_ (⊤ : T'.Opens)) ≫ b.1 := by
          rw [show (⊤ : T'.Opens).ι ≫ T'.topIso.inv = 𝟙 _ from T'.topIso.hom_inv_id,
            Category.id_comp]
      _ = (i ⁻¹ᵁ (⊤ : T'.Opens)).ι ≫ a := b.2.2

end Assembly

/-! ### The four criteria -/

/-- Formal smoothness of the ring map on sections over a compatible pair of affine opens is
formal smoothness of the restricted morphism, through `AlgebraicGeometry.arrowResLEAppIso`. -/
private theorem formallySmooth_appLE_iff_formallySmooth_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    (f.appLE V U hUV).hom.FormallySmooth ↔ AlgebraicGeometry.FormallySmooth (f.resLE V U hUV) := by
  have _ : IsAffine (U : Scheme.{u}) := hU
  have _ : IsAffine (V : Scheme.{u}) := hV
  rw [formallySmooth_iff_appTop_formallySmooth]
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U hUV)).symm

/-- **Criterion (1) implies criterion (3) of [Stacks Project, Tag 0D0F].** -/
theorem formallySmooth_appLE_of_formallySmooth {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : AlgebraicGeometry.FormallySmooth f) (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens)
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) : (f.appLE V U hUV).hom.FormallySmooth :=
  (formallySmooth_appLE_iff_formallySmooth_resLE f hU hV hUV).mpr (hf.resLE U V hUV)

/-- **Criterion (3) implies criterion (1) on a compatible pair of affine opens**, the chart
dictionary of [Stacks Project, Tag 02H4] read through
`AlgebraicGeometry.arrowResLEAppIso`. -/
theorem formallySmooth_resLE_of_formallySmooth_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)
    (hfs : (f.appLE V U hUV).hom.FormallySmooth) :
    AlgebraicGeometry.FormallySmooth (f.resLE V U hUV) :=
  (formallySmooth_appLE_iff_formallySmooth_resLE f hU hV hUV).mp hfs

/-- **Criterion (2) implies criterion (3) of [Stacks Project, Tag 0D0F].** Formal smoothness of
the ring maps on sections is an affine-local property of a morphism,
`Stacks.Smooth.FormallySmoothAffineLocally`, so it may be checked at the points of the
source. -/
theorem formallySmooth_appLE_of_exists_formallySmooth_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ x : X, ∃ (U : X.Opens) (V : Y.Opens), x ∈ U ∧ f.base x ∈ V ∧
      ∃ hUV : U ≤ f ⁻¹ᵁ V, AlgebraicGeometry.FormallySmooth (f.resLE V U hUV))
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) : (f.appLE V U hUV).hom.FormallySmooth := by
  refine (formallySmoothAffineLocally_iff_appLE f).mp
    (formallySmoothAffineLocally_of_exists_formallySmooth_resLE f (fun x => ?_))
    ⟨V, hV⟩ ⟨U, hU⟩ hUV
  obtain ⟨U₀, V₀, hxU, -, hUV₀, hfs⟩ := H x
  exact ⟨V₀, U₀, hxU, hUV₀, formallySmooth_of_formallySmoothScheme hfs⟩

/-- **Criterion (4) implies criterion (2) of [Stacks Project, Tag 0D0F].** The charts of the
coverings are themselves neighbourhoods on which the restricted morphism is formally smooth. -/
theorem exists_formallySmooth_resLE_of_affineOpenCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    {J : Type u} {V : J → Y.Opens} (hV : IsOpenCover V) (hVaff : ∀ j, IsAffineOpen (V j))
    (hf : ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
      (∀ i, IsAffineOpen (U i)) ∧
        ∀ i, (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom.FormallySmooth) (x : X) :
    ∃ (U : X.Opens) (W : Y.Opens), x ∈ U ∧ f.base x ∈ W ∧
      ∃ hUW : U ≤ f ⁻¹ᵁ W, AlgebraicGeometry.FormallySmooth (f.resLE W U hUW) := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hV.iSup_eq_top ▸ Opens.mem_top (f.base x))
  obtain ⟨I, U, hU, hUaff, hUfs⟩ := hf j
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hU ▸ show x ∈ f ⁻¹ᵁ V j from hj)
  exact ⟨U k, V j, hk, hj, (le_iSup U k).trans hU.le,
    formallySmooth_resLE_of_formallySmooth_appLE f (hUaff k) (hVaff j) _ (hUfs k)⟩

/-- **[Stacks Project, Tag 0D0F].** For a morphism of schemes `f : X ⟶ Y` the following are
equivalent: `f` is formally smooth; `f` is formally smooth on a neighbourhood of every point of
`X`; the ring map `Γ(Y, V) ⟶ Γ(X, U)` is formally smooth for every pair of affine opens with
`f(U) ⊆ V`; and there is one affine open covering of `Y` together with, over each of its
members, an affine open covering of its inverse image, on whose charts those ring maps are
formally smooth.

The implications `1 → 3`, `1 → 2`, `3 → 4`, `4 → 2` and `2 → 3` are the formal manipulations of
[Stacks Project, Tag 02H3] and the affine criterion [Stacks Project, Tag 02H4] together with the
affine-locality of formal smoothness of ring maps. The remaining implication `3 → 1` is
`Stacks.Smooth.formallySmooth_of_formallySmooth_appLE`, the torsor argument of the source, whose
pseudo-torsor is `Stacks.Smooth.isLiftPseudoTorsor`. -/
@[stacks 0D0F "all four criteria, for an arbitrary morphism of schemes"]
theorem formallySmooth_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE
      [AlgebraicGeometry.FormallySmooth f,
        ∀ x : X, ∃ (U : X.Opens) (V : Y.Opens), x ∈ U ∧ f.base x ∈ V ∧
          ∃ hUV : U ≤ f ⁻¹ᵁ V, AlgebraicGeometry.FormallySmooth (f.resLE V U hUV),
        ∀ U : X.Opens, IsAffineOpen U → ∀ V : Y.Opens, IsAffineOpen V →
          ∀ hUV : U ≤ f ⁻¹ᵁ V, (f.appLE V U hUV).hom.FormallySmooth,
        ∃ (J : Type u) (V : J → Y.Opens), IsOpenCover V ∧ (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i, (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom.FormallySmooth] := by
  tfae_have 1 → 2 := fun hf x =>
    ⟨⊤, ⊤, trivial, trivial, le_of_eq f.preimage_top.symm,
      hf.resLE ⊤ ⊤ (le_of_eq f.preimage_top.symm)⟩
  tfae_have 1 → 3 := formallySmooth_appLE_of_formallySmooth
  tfae_have 2 → 3 := formallySmooth_appLE_of_exists_formallySmooth_resLE f
  tfae_have 3 → 4 := exists_affineOpenCover_of_formallySmooth_appLE f
  tfae_have 4 → 2 := fun ⟨_, _, hV, hVaff, hf⟩ =>
    exists_formallySmooth_resLE_of_affineOpenCover f hV hVaff hf
  tfae_have 3 → 1 := formallySmooth_of_formallySmooth_appLE f
  tfae_finish

end Stacks.Smooth

end
