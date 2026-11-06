module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafInverseImageSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemSectionsColimit
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects

/-!
# Sections of the colimit of a system of sheaves of sets over a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine transition
morphisms, let `(F_i, φ_{i'i})` be a system of sheaves of sets on the small étale sites of the
`X_i` ([Stacks, Tag 0EZL]) and let `𝓖 = colim f_i⁻¹F_i` on the small étale site of `X`. For an
object `V₀` of the small étale site of a stage `X_{i₀}` whose underlying scheme is quasi-compact
and quasi-separated, with base changes `V_k = V₀ ×_{X_{i₀}} X_k` and `V = V₀ ×_{X_{i₀}} X`,

`𝓖(V) = colim_{k ≥ i₀} F_k(V_k)`.

This is the degree zero case of [Stacks, Tag 09YQ] for sheaves of sets, stated elementwise with
the maps of the colimit given by maps of sheaves on the small étale site of `X_{i₀}`. It rests on
two colimit formulas: the sections over `V` of a colimit of a system of sheaves of sets are the
colimit of the sections (the degree zero case of [Stacks, Tag 0739], deduced from
[Stacks, Tag 0738] since `V` is covered by finitely many affine objects with quasi-compact
overlaps), and the sections over `V` of a single inverse image `f_k⁻¹F_k` are the colimit of the
sections of the `f_{lk}⁻¹F_k` over `V_l` ([Stacks, Tag 09YN],
`Stacks.EtaleCohomology.Sets.exists_pullbackSectionsMap_eq_of_isLimit`).

## Main definitions

* `Stacks.EtaleCohomology.Sets.pushforwardLeg`: the map `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖`.
* `Stacks.EtaleCohomology.Sets.pushforwardTransition`: the map `f_{k i₀,*}F_k ⟶ f_{l i₀,*}F_l`.

## Main results

* `Stacks.EtaleCohomology.isQuasiCompactObject_of_compactSpace`: an object of the small étale site
  with quasi-compact underlying scheme is a quasi-compact object of the site.
* `Stacks.EtaleCohomology.Sets.exists_sections_eq_of_isSystemColimit`,
  `Stacks.EtaleCohomology.Sets.exists_transition_eq_of_isSystemColimit`: sections of a colimit of
  sheaves of sets over a quasi-compact and quasi-separated object.
* `Stacks.EtaleCohomology.Sets.exists_pushforwardLeg_apply_eq`,
  `Stacks.EtaleCohomology.Sets.exists_pushforwardTransition_apply_eq`: the degree zero case of
  [Stacks, Tag 09YQ] for sheaves of sets.

## Implementation notes

The proofs are those of `Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardLeg_apply_eq`
and `Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardTransition_apply_eq_zero` for
abelian sheaves, with the vanishing of one section replaced by the agreement of two.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Sections of a colimit over a quasi-compact quasi-separated object -/

section QuasiCompact

variable {X : Scheme.{u}}

/-- **An object of the small étale site with quasi-compact underlying scheme is a quasi-compact
object of the site** (Stacks 090H): every covering of it is refined by a finite covering by
objects with affine underlying scheme. -/
theorem isQuasiCompactObject_of_compactSpace (V : X.Etale) [CompactSpace V.left] :
    (smallEtaleTopology X).IsQuasiCompactObject V := by
  refine GrothendieckTopology.isQuasiCompactObject_of_exists_finite_refinement fun 𝒰 h𝒰 => ?_
  obtain ⟨E, hfin, -, hE, hle⟩ := exists_finite_isAffine_covering_le V 𝒰.sieve₀ h𝒰
  choose j a ha using fun i : E.I₀ => (Sieve.mem_ofArrows_iff 𝒰.X 𝒰.f (E.f i)).1
    (hle _ (E.sieve₀_f i))
  let E' := E.restrictIndex (Equiv.ulift.{max (u + 1) u} : ULift E.I₀ ≃ E.I₀)
  have hsieve : E'.sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_restrictIndex_equiv Equiv.ulift)
  exact ⟨E', ⟨fun i => j i.down, fun i => a i.down, fun i => (ha i.down).symm⟩, hsieve ▸ hE,
    (inferInstance : Finite (ULift E.I₀))⟩

/-- **Finite coverings by quasi-compact objects with quasi-compact overlaps.** Every covering of
an object of the small étale site with quasi-compact and quasi-separated underlying scheme is
refined by a finite covering whose members and their pairwise fibre products are quasi-compact
objects of the site. This is hypothesis (4) of [Stacks, Tag 0738]. -/
theorem exists_finite_quasiCompact_covering_le (U : X.Etale) (hU : U ∈ qcqsEtaleObjects X)
    (S : Sieve U) (hS : S ∈ smallEtaleTopology X U) :
    ∃ 𝒱 : PreZeroHypercover.{max (u + 1) u} U, Finite 𝒱.I₀ ∧ 𝒱.sieve₀ ∈ smallEtaleTopology X U ∧
      𝒱.sieve₀ ≤ S ∧ ∀ j j' : 𝒱.I₀, ∃ (W : X.Etale) (p : W ⟶ 𝒱.X j) (q : W ⟶ 𝒱.X j'),
        IsPullback p q (𝒱.f j) (𝒱.f j') ∧ (smallEtaleTopology X).IsQuasiCompactObject W := by
  obtain ⟨E, ⟨hfin, -, hEX, hE⟩, -, hle⟩ := exists_qcqsCovering_le U hU S hS
  let E' := E.restrictIndex (Equiv.ulift.{max (u + 1) u} : ULift E.I₀ ≃ E.I₀)
  have hsieve : E'.sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_restrictIndex_equiv Equiv.ulift)
  refine ⟨E', (inferInstance : Finite (ULift E.I₀)), hsieve ▸ hE, hsieve ▸ hle, fun j j' => ?_⟩
  obtain ⟨t, ⟨ht⟩, htm⟩ := exists_pullbackCone_mem_qcqsEtaleObjects (E.f j.down) (E.f j'.down)
    (hEX _) (hEX _) hU
  have := htm.1
  exact ⟨t.pt, t.fst, t.snd, IsPullback.of_isLimit ht, isQuasiCompactObject_of_compactSpace t.pt⟩

end QuasiCompact

namespace Sets

section SystemSections

variable {X : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {G : Iᵒᵖ → Sheaf X.smallEtaleTopology (Type (u + 1))} {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (G j ⟶ G i)}
  (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)
  {𝓕 : Sheaf X.smallEtaleTopology (Type (u + 1))} {ι : ∀ i, G i ⟶ 𝓕}
  (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ι i = ι j) (h : IsSystemColimit G T 𝓕 ι)

include h in
/-- **Sections of a colimit of a system of sheaves of sets over a quasi-compact quasi-separated
object** (the degree zero case of [Stacks, Tag 0739]): the sections functor carries the colimit
cocone of the functor attached to the system to a colimit cocone. -/
theorem isColimit_mapCocone_sheafSections_of_isSystemColimit (V : X.Etale)
    (hV : V ∈ qcqsEtaleObjects X) :
    Nonempty (IsColimit (((sheafSections X.smallEtaleTopology (Type (u + 1))).obj (op V)).mapCocone
      (SystemLift.cocone hT ι hι))) := by
  obtain ⟨hc⟩ := (SystemLift.isSystemColimit_iff hT ι hι).mp h
  let F := SystemLift.functor G (fun a => T a) hT
  let S := (sheafSections X.smallEtaleTopology (Type (u + 1))).obj (op V)
  have : IsIso (colimit.post F S) := (isIso_iff_bijective _).mpr <|
    (Sheaf.injective_and_bijective_colimit_post_sheafSections X.smallEtaleTopology F V).2.2.2
      (exists_finite_quasiCompact_covering_le V hV)
  have := preservesColimit_of_isIso_post S F
  exact ⟨isColimitOfPreserves S hc⟩

include hT hι h in
/-- **Every section of a colimit of a system of sheaves of sets over a quasi-compact
quasi-separated object comes from a stage.** -/
theorem exists_sections_eq_of_isSystemColimit (V : X.Etale) (hV : V ∈ qcqsEtaleObjects X)
    (s : 𝓕.obj.obj (op V)) :
    ∃ (i : Iᵒᵖ) (x : (G i).obj.obj (op V)), (ι i).hom.app (op V) x = s := by
  obtain ⟨hc⟩ := isColimit_mapCocone_sheafSections_of_isSystemColimit hT hι h V hV
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective _ hc s
  exact ⟨Opposite.op j.idx, y, hy⟩

include hT hι h in
/-- **Two sections of a stage with the same image in a colimit of a system of sheaves of sets over
a quasi-compact quasi-separated object agree after a transition map.** -/
theorem exists_transition_eq_of_isSystemColimit (V : X.Etale) (hV : V ∈ qcqsEtaleObjects X)
    {i : Iᵒᵖ} (x x' : (G i).obj.obj (op V))
    (hx : (ι i).hom.app (op V) x = (ι i).hom.app (op V) x') :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i), (T a).hom.app (op V) x = (T a).hom.app (op V) x' := by
  obtain ⟨hc⟩ := isColimit_mapCocone_sheafSections_of_isSystemColimit hT hι h V hV
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc
    (i := SystemLift.mk i.unop 0) (j := SystemLift.mk i.unop 0) (xi := x) (xj := x')).mp hx
  obtain rfl : f = g := Subsingleton.elim _ _
  have hk : SystemLift.mk i.unop 0 ≤ k := leOfHom f
  refine ⟨Opposite.op k.idx, (homOfLE (SystemLift.idx_le_idx hk)).op, ?_⟩
  change (SystemLift.map G (fun a => T a) hk).hom.app (op V) x =
    (SystemLift.map G (fun a => T a) hk).hom.app (op V) x' at hfg
  by_cases hlt : (SystemLift.mk i.unop 0).lvl < k.lvl
  · rwa [SystemLift.map_of_lt G (fun a => T a) hk hlt] at hfg
  · obtain rfl := SystemLift.eq_of_le_of_not_lt hk hlt
    rw [SystemLift.map_self] at hfg
    exact congrArg _ hfg

end SystemSections

/-! ### The system of sections over the stages -/

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)



section Legs

variable (F : EtaleSheafSystem D (Type (u + 1)))
  {𝓖 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
  (ι : ∀ i : Iᵒᵖ,
    (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app i)).obj (F.obj i) ⟶ 𝓖)

/-- The leg `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` on the small étale site of `X_{i₀}`: the direct image of
the map `F_k ⟶ f_{k,*}𝓖` adjoint to `ι_k`, followed by `f_{k i₀,*}f_{k,*} = f_{i₀,*}`. -/
def pushforwardLeg {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    (systemPushforward D (Type (u + 1)) a).obj (F.obj k) ⟶
      (smallEtalePushforward (X := c.pt) (c.π.app i₀) (Type (u + 1))).obj 𝓖 :=
  (systemPushforward D (Type (u + 1)) a).map
      ((smallEtaleSheafAdjunction (Type (u + 1)) (X := c.pt) (c.π.app k)).homEquiv _ _ (ι k)) ≫
    (smallEtalePushforwardComp' (X := c.pt) (c.π.app k) (D.map a) (c.π.app i₀) (c.w a).symm
      (Type (u + 1))).hom.app 𝓖

/-- The transition `f_{k i₀,*}F_k ⟶ f_{l i₀,*}F_l` on the small étale site of `X_{i₀}`: the
direct image of the transition map of the system in adjoint form, followed by
`f_{k i₀,*}f_{l k,*} = f_{l i₀,*}`. -/
def pushforwardTransition {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀) :
    (systemPushforward D (Type (u + 1)) a).obj (F.obj k) ⟶
      (systemPushforward D (Type (u + 1)) (b ≫ a)).obj (F.obj l) :=
  (systemPushforward D (Type (u + 1)) a).map (F.transition b) ≫
    (systemPushforwardComp D (Type (u + 1)) b a).hom.app (F.obj l)

/-- The component of the leg at an object, on sections: the image of a section under the unit,
mapped by `ι_k`, and restricted along the comparison of the base changes. -/
lemma pushforwardLeg_app_apply {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (D.obj i₀).Etale)
    (x : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))) :
    (pushforwardLeg c F ι a).hom.app (op V₀) x =
      𝓖.obj.map ((smallEtaleBaseChangeComp' (W := c.pt) (c.π.app k) (D.map a) (c.π.app i₀)
          (c.w a).symm).hom.app V₀).op
        ((ι k).hom.app _ (smallEtaleSheafPullbackUnitApp (c.π.app k) (F.obj k) _ x)) := by
  rfl

/-- The component of the transition at an object, on sections. -/
lemma pushforwardTransition_app_apply {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀)
    (V₀ : (D.obj i₀).Etale)
    (x : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))) :
    (pushforwardTransition F b a).hom.app (op V₀) x =
      (F.obj l).obj.map ((smallEtaleBaseChangeComp' (D.map b) (D.map a) (D.map (b ≫ a))
          (D.map_comp b a)).hom.app V₀).op
        ((F.map b).hom.app _ (smallEtaleSheafPullbackUnitApp (D.map b) (F.obj k) _ x)) := by
  rfl


/-- The map `f_{k i₀,*}F_k ⟶ f_{i₀,*}f_k⁻¹F_k` on the small étale site of `X_{i₀}`: the direct
image of the unit of `f_k⁻¹ ⊣ f_{k,*}`, followed by `f_{k i₀,*}f_{k,*} = f_{i₀,*}`. -/
def pushforwardUnit {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    (systemPushforward D (Type (u + 1)) a).obj (F.obj k) ⟶
      (smallEtalePushforward (X := c.pt) (c.π.app i₀) (Type (u + 1))).obj
        ((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app k)).obj (F.obj k)) :=
  (systemPushforward D (Type (u + 1)) a).map
      ((smallEtaleSheafAdjunction (Type (u + 1)) (X := c.pt) (c.π.app k)).unit.app (F.obj k)) ≫
    (smallEtalePushforwardComp' (X := c.pt) (c.π.app k) (D.map a) (c.π.app i₀) (c.w a).symm
      (Type (u + 1))).hom.app _

/-- The component of `pushforwardUnit` at an object, on sections. -/
lemma pushforwardUnit_app_apply {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (D.obj i₀).Etale)
    (x : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))) :
    (pushforwardUnit c F a).hom.app (op V₀) x =
      ((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app k)).obj (F.obj k)).obj.map
        ((smallEtaleBaseChangeComp' (W := c.pt) (c.π.app k) (D.map a) (c.π.app i₀)
          (c.w a).symm).hom.app V₀).op
        (smallEtaleSheafPullbackUnitApp (c.π.app k) (F.obj k) _ x) := by
  rfl

/-- The leg `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` factors through `f_{i₀,*}f_k⁻¹F_k`. -/
lemma pushforwardUnit_comp_map {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    pushforwardUnit c F a ≫
        (smallEtalePushforward (X := c.pt) (c.π.app i₀) (Type (u + 1))).map (ι k) =
      pushforwardLeg c F ι a := by
  rw [pushforwardUnit, pushforwardLeg, Adjunction.homEquiv_unit, Category.assoc,
    ← NatTrans.naturality, Functor.comp_map, Functor.map_comp, Category.assoc]

/-- **The units of the inverse images intertwine the transition maps of a system** with the maps
of the diagram of its inverse images to the limit. -/
lemma pushforwardUnit_comp_map_pullbackDiagramMap {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀) :
    pushforwardUnit c F a ≫
        (smallEtalePushforward (X := c.pt) (c.π.app i₀) (Type (u + 1))).map
          (EtaleSheafSystem.sheafPullbackDiagramMap (A := Type (u + 1)) F c (i := l) (j := k) b) =
      pushforwardTransition F b a ≫ pushforwardUnit c F (b ≫ a) := by
  have hcoc := congrArg (fun z => NatTrans.app (Iso.hom z)
      ((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app l)).obj (F.obj l)))
    (smallEtalePushforwardComp'_assoc (c.π.app l) (D.map b) (D.map a) (c.π.app k) (c.w b).symm
      (D.map (b ≫ a)) (D.map_comp b a) (c.π.app i₀) (c.w a).symm (c.w (b ≫ a)).symm (Type (u + 1)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hcoc
  rw [pushforwardUnit, Category.assoc, ← NatTrans.naturality, Functor.comp_map, ← Category.assoc,
    ← Functor.map_comp, ← Adjunction.homEquiv_unit,
    EtaleSheafSystem.sheafPullbackDiagramMap_eq (A := Type (u + 1)) F c b, Equiv.apply_symm_apply,
    pushforwardTransition, pushforwardUnit, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Category.assoc]
  congr 1
  rw [← reassoc_of% ((systemPushforwardComp D (Type (u + 1)) b a).hom.naturality
    ((smallEtaleSheafAdjunction (Type (u + 1)) (X := c.pt) (c.π.app l)).unit.app (F.obj l)))]
  exact congrArg _ hcoc

/-- **The transition maps pushed to a stage compose.** -/
lemma pushforwardTransition_comp {m l k i₀ : Iᵒᵖ} (e : m ⟶ l) (b : l ⟶ k) (a : k ⟶ i₀) :
    pushforwardTransition F b a ≫ pushforwardTransition F e (b ≫ a) =
      pushforwardTransition F (e ≫ b) a := by
  have hcoc := congrArg (fun z => NatTrans.app (Iso.hom z) (F.obj m))
    (smallEtalePushforwardComp'_assoc (D.map e) (D.map b) (D.map a) (D.map (e ≫ b))
      (D.map_comp e b) (D.map (b ≫ a)) (D.map_comp b a) (D.map ((e ≫ b) ≫ a))
      (D.map_comp (e ≫ b) a) (D.map_comp e (b ≫ a)) (Type (u + 1)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hcoc
  simp only [pushforwardTransition, F.transition_comp e b, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ((systemPushforwardComp D (Type (u + 1)) b a).hom.naturality (F.transition e))]
  exact congrArg _ (congrArg _ hcoc.symm)



end Legs

/-! ### The degree zero colimit -/

section DegreeZero

variable [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]

variable (hc : IsLimit c) (F : EtaleSheafSystem D (Type (u + 1)))
  {𝓖 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
  (ι : ∀ i : Iᵒᵖ,
    (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app i)).obj (F.obj i) ⟶ 𝓖)
  (hι : EtaleSheafSystem.IsSheafPullbackCocone (A := Type (u + 1)) F c ι)
  (hpres : EtaleSheafSystem.IsSheafPullbackColimitPresentation (A := Type (u + 1)) F c 𝓖 ι)

include hc hι hpres in
/-- **Every section of the colimit over the base change of a quasi-compact separated object comes
from a stage** (the surjectivity half of the degree zero case of Stacks 09YQ). -/
theorem exists_pushforwardLeg_apply_eq {i₀ : Iᵒᵖ} (V₀ : (D.obj i₀).Etale)
    [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left]
    (s : 𝓖.obj.obj (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))) :
    ∃ (k : Iᵒᵖ) (a : k ⟶ i₀)
      (x : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))),
      (pushforwardLeg c F ι a).hom.app (op V₀) x = s := by
  have hV := mem_qcqsEtaleObjects_smallEtaleBaseChange_obj c hc V₀
  let V := (smallEtaleBaseChange (c.π.app i₀)).obj V₀
  obtain ⟨j₁, y, hy⟩ := exists_sections_eq_of_isSystemColimit
    (EtaleSheafSystem.sheafPullbackDiagramMap_comp (A := Type (u + 1)) F c) (fun a => hι a) hpres
    V hV s
  obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁.unop i₀.unop
  let b₁ : op j ⟶ j₁ := (homOfLE h₁).op
  let a : op j ⟶ i₀ := (homOfLE h₂).op
  let y₂ := (EtaleSheafSystem.sheafPullbackDiagramMap (A := Type (u + 1)) F c (i := op j) (j := j₁)
    b₁).hom.app (op V) y
  have hy₂ : (ι (op j)).hom.app (op V) y₂ = s :=
    (congrArg (fun φ => φ.hom.app (op V) y) (hι b₁)).trans hy
  let W := (smallEtaleBaseChange (D.map a)).obj V₀
  let ε := (smallEtaleBaseChangeComp' (W := c.pt) (c.π.app (op j)) (D.map a) (c.π.app i₀)
    (c.w a).symm).app V₀
  let Gj := (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app (op j))).obj (F.obj (op j))
  let y₃ := Gj.obj.map ε.inv.op y₂
  have : CompactSpace W.left := compactSpace_smallEtaleBaseChange_obj (D.map a) V₀ inferInstance
  have : QuasiSeparatedSpace W.left :=
    quasiSeparatedSpace_smallEtaleBaseChange_obj (D.map a) V₀ inferInstance
  obtain ⟨k, b, t, ht⟩ := exists_pullbackSectionsMap_eq_of_isLimit hc (F.obj (op j)) W y₃
  let C2 := smallEtaleBaseChangeComp' (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a)
  let C3 := smallEtaleBaseChangeComp' (W := c.pt) (c.π.app k) (D.map b) (c.π.app (op j))
    (c.w b).symm
  let C := smallEtaleBaseChangeComp' (W := c.pt) (c.π.app k) (D.map (b ≫ a)) (c.π.app i₀)
    (c.w (b ≫ a)).symm
  let W' := (smallEtaleBaseChange (D.map b)).obj W
  let c2 : (smallEtaleBaseChange (D.map (b ≫ a))).obj V₀ ⟶ W' := C2.hom.app V₀
  refine ⟨k, b ≫ a, (F.obj k).obj.map c2.op ((F.map b).hom.app _ t), ?_⟩
  -- the comparison of the two ways of reaching `V`
  have hmor : C.hom.app V₀ ≫ (smallEtaleBaseChange (c.π.app k)).map c2 =
      ε.hom ≫ C3.hom.app W := by
    have h := NatTrans.congr_app (smallEtaleBaseChangeComp'_assoc (c.π.app k) (D.map b) (D.map a)
      (c.π.app (op j)) (c.w b).symm (D.map (b ≫ a)) (D.map_comp b a) (c.π.app i₀)
      (c.w a).symm (c.w (b ≫ a)).symm) V₀
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Category.comp_id] at h
    exact h
  -- the sections
  let O2 := (smallEtaleBaseChange (c.π.app k)).obj W'
  let Gk := (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app k)).obj (F.obj k)
  let M := (smallEtaleBaseChange (c.π.app k)).map c2
  let ψt := smallEtaleSheafPullbackSectionsMap (c.π.app k) (D.map b) (c.π.app (op j)) (c.w b).symm
    (F.obj (op j)) W' t
  have hιb : (smallEtaleSheafPullbackCompApp (Type (u + 1)) (X := c.pt) (c.π.app k) (D.map b)
        (c.π.app (op j)) (c.w b).symm (F.obj (op j))).hom ≫ ι (op j) =
      (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app k)).map (F.map b) ≫ ι k := by
    rw [← hι b, EtaleSheafSystem.sheafPullbackDiagramMap, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have e : (ι k).hom.app (op O2)
      (((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app k)).map (F.map b)).hom.app
        (op O2) (smallEtaleSheafPullbackUnitApp (c.π.app k) _ W' t)) =
        (ι (op j)).hom.app (op O2) ψt :=
    (congrArg (fun φ => φ.hom.app (op O2) (smallEtaleSheafPullbackUnitApp (c.π.app k) _ W' t))
      hιb).symm
  have hιn : ∀ (m : Iᵒᵖ) {O O' : c.pt.Etale} (g : O ⟶ O')
      (z : ((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app m)).obj
        (F.obj m)).obj.obj (op O')),
      (ι m).hom.app (op O) (((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt)
        (c.π.app m)).obj (F.obj m)).obj.map g.op z) = 𝓖.obj.map g.op ((ι m).hom.app (op O') z) :=
    fun m _ _ g z => congrArg (fun φ => φ z) ((ι m).hom.naturality g.op)
  let c3 : (smallEtaleBaseChange (c.π.app (op j))).obj W ⟶ O2 := C3.hom.app W
  have hy₃ : Gj.obj.map ε.hom.op y₃ = y₂ := by
    show Gj.obj.map ε.hom.op (Gj.obj.map ε.inv.op y₂) = y₂
    rw [presheaf_map_map_apply_types, Iso.hom_inv_id, op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply]
  calc _ = 𝓖.obj.map (C.hom.app V₀).op ((ι k).hom.app _ (Gk.obj.map M.op
          (((smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app k)).map (F.map b)).hom.app
            (op O2) (smallEtaleSheafPullbackUnitApp (c.π.app k) _ W' t)))) := by
        rw [pushforwardLeg_app_apply, smallEtaleSheafPullbackUnitApp_naturality,
          smallEtaleSheafPullbackUnitApp_map]
        rfl
    _ = 𝓖.obj.map (C.hom.app V₀).op (𝓖.obj.map M.op ((ι (op j)).hom.app _ ψt)) := by
        rw [hιn, e]
    _ = 𝓖.obj.map ε.hom.op (𝓖.obj.map c3.op ((ι (op j)).hom.app (op O2) ψt)) := by
        rw [presheaf_map_map_apply_types, presheaf_map_map_apply_types, hmor]
    _ = 𝓖.obj.map ε.hom.op ((ι (op j)).hom.app _ y₃) :=
        congrArg (𝓖.obj.map ε.hom.op) ((hιn _ c3 ψt).symm.trans
          (congrArg ((ι (op j)).hom.app _) ht))
    _ = s :=
        (hιn _ ε.hom y₃).symm.trans ((congrArg ((ι (op j)).hom.app (op V)) hy₃).trans hy₂)

include hι in
/-- The legs `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` are compatible with the transition maps. -/
lemma pushforwardTransition_comp_pushforwardLeg {l k i₀ : Iᵒᵖ} (b : l ⟶ k)
    (a : k ⟶ i₀) :
    pushforwardTransition F b a ≫ pushforwardLeg c F ι (b ≫ a) = pushforwardLeg c F ι a := by
  rw [← pushforwardUnit_comp_map c F ι (b ≫ a), ← Category.assoc,
    ← pushforwardUnit_comp_map_pullbackDiagramMap c F b a, Category.assoc, ← Functor.map_comp,
    hι b, pushforwardUnit_comp_map c F ι a]

include hc hι hpres in
/-- **Two sections of a stage with the same image in the colimit agree at a later stage** (the
injectivity half of the degree zero case of [Stacks, Tag 09YQ] for sheaves of sets). -/
theorem exists_pushforwardTransition_apply_eq {i₀ : Iᵒᵖ}
    (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left] {k : Iᵒᵖ}
    (a : k ⟶ i₀) (x x' : (F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))
    (hx : (pushforwardLeg c F ι a).hom.app (op V₀) x =
      (pushforwardLeg c F ι a).hom.app (op V₀) x') :
    ∃ (l : Iᵒᵖ) (b : l ⟶ k), (pushforwardTransition F b a).hom.app (op V₀) x =
      (pushforwardTransition F b a).hom.app (op V₀) x' := by
  have hV := mem_qcqsEtaleObjects_smallEtaleBaseChange_obj c hc V₀
  have hu : (ι k).hom.app _ ((pushforwardUnit c F a).hom.app (op V₀) x) =
      (ι k).hom.app _ ((pushforwardUnit c F a).hom.app (op V₀) x') :=
    ((congrArg (fun φ => φ.hom.app (op V₀) x) (pushforwardUnit_comp_map c F ι a)).trans hx).trans
      (congrArg (fun φ => φ.hom.app (op V₀) x') (pushforwardUnit_comp_map c F ι a)).symm
  obtain ⟨l, b, hb⟩ := exists_transition_eq_of_isSystemColimit
    (EtaleSheafSystem.sheafPullbackDiagramMap_comp (A := Type (u + 1)) F c) (fun a => hι a) hpres _
    hV _ _ hu
  let z := (pushforwardTransition F b a).hom.app (op V₀) x
  let z' := (pushforwardTransition F b a).hom.app (op V₀) x'
  have hz : (pushforwardUnit c F (b ≫ a)).hom.app (op V₀) z =
      (pushforwardUnit c F (b ≫ a)).hom.app (op V₀) z' :=
    (congrArg (fun φ => φ.hom.app (op V₀) x)
      (pushforwardUnit_comp_map_pullbackDiagramMap c F b a)).symm.trans <| hb.trans <|
      congrArg (fun φ => φ.hom.app (op V₀) x') (pushforwardUnit_comp_map_pullbackDiagramMap c F b a)
  let Gl := (smallEtaleSheafPullback (Type (u + 1)) (X := c.pt) (c.π.app l)).obj (F.obj l)
  let ε := (smallEtaleBaseChangeComp' (W := c.pt) (c.π.app l) (D.map (b ≫ a)) (c.π.app i₀)
    (c.w (b ≫ a)).symm).app V₀
  have hz' : smallEtaleSheafPullbackUnitApp (c.π.app l) (F.obj l) _ z =
      smallEtaleSheafPullbackUnitApp (c.π.app l) (F.obj l) _ z' := by
    have h3 := congrArg (Gl.obj.map ε.inv.op)
      (((pushforwardUnit_app_apply c F (b ≫ a) V₀ z).symm.trans hz).trans
        (pushforwardUnit_app_apply c F (b ≫ a) V₀ z'))
    change Gl.obj.map ε.inv.op (Gl.obj.map ε.hom.op _) =
      Gl.obj.map ε.inv.op (Gl.obj.map ε.hom.op _) at h3
    rwa [presheaf_map_map_apply_types, presheaf_map_map_apply_types, Iso.inv_hom_id, op_id,
      Functor.map_id_apply, Functor.map_id_apply] at h3
  have : CompactSpace ((smallEtaleBaseChange (D.map (b ≫ a))).obj V₀).left :=
    compactSpace_smallEtaleBaseChange_obj (D.map (b ≫ a)) V₀ inferInstance
  obtain ⟨m, e, he⟩ :=
    exists_smallEtaleSheafPullbackUnitApp_eq_of_isLimit D c hc (F.obj l) _ z z' hz'
  refine ⟨m, e ≫ b, ?_⟩
  rw [← pushforwardTransition_comp F e b a]
  exact congrArg (fun w => (F.obj m).obj.map _ ((F.map e).hom.app _ w)) he

end DegreeZero
end Sets

end Stacks.EtaleCohomology

end
