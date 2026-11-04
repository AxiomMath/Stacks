module

public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjectsTwoIso
public import StacksFrontier.AlgebraicGeometry.Stacks.GluedChartSchemePointDecomposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.CategoryTheory.Sites.Stack.DisjointCoverFiberMorphism
public import StacksFrontier.CategoryTheory.Sites.Stack.OverIsStack

/-!
# Formal smoothness on objects of a scheme-valued point assembled from a family

Let `𝒴` be a category fibred in groupoids over the big fppf site of `S` which is a stack for the
fppf topology, let the underlying scheme of `W` be the coproduct of the underlying schemes of a
family `Z i` of objects of the site, and let `g : (Sch/W)_{fppf} ⟶ 𝒴` be a scheme-valued point of
`𝒴` whose restriction to each summand is 2-isomorphic to a given `f i`. This file proves that `g`
is formally smooth on objects (**Stacks 06D0**) as soon as every `f i` is.

Unlike surjectivity on objects, which passes to `g` from a *single* member of the family, formal
smoothness on objects is universal over the objects of the source, and an affine object of the
site mapping to `W` need not land in a single summand. What replaces the single-member argument
is the finite clopen decomposition of
`AlgebraicGeometry.BigFppfOver.exists_thickened_decomposition_of_hom_coproduct`: a first-order
thickening of affine objects of the site, together with a morphism of its closed member to `W`,
decomposes into finitely many first-order thickenings of affine objects each of whose closed
members maps into a single summand. The members' lifting properties are applied piece by piece
and the results glued, which is where the stack condition on `𝒴` enters.

## Main results

* `AlgebraicGeometry.Stack.hasFirstOrderObjectLifts_of_isColimit_of_forall`: the first-order
  lifting property of `AlgebraicGeometry.Stack.HasFirstOrderObjectLifts` for the assembled
  point, from that of the members.
* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_isColimit_of_forall`: **Stacks 06D0** for
  the assembled point, from Stacks 06D0 for the members.

## Implementation notes

The members' hypotheses are first transported along the restriction 2-isomorphisms by
`AlgebraicGeometry.Stack.hasFirstOrderObjectLifts_of_iso`, so that the whole argument runs with
the single functor underlying `g` and no component of a 2-isomorphism appears in it.

Three things are glued over the decomposition, and all three gluings are of the shape "a disjoint
covering family imposes no compatibility condition":

* the arrow `U' ⟶ W` underlying the lifted object, as a section of the representable sheaf `h_W`
  over the decomposition of `U'`
  (`AlgebraicGeometry.BigFppfOver.existsUnique_section_of_disjoint_openCover`);
* the vertical identification of its `g`-image with the given object of `𝒴` over `U'`
  (`CategoryTheory.Functor.exists_fiberHom_of_disjointCover`, which is condition (2) of
  **Stacks 026F** for `𝒴`);
* the compatibility equation, by the separatedness statement
  `CategoryTheory.Functor.eq_of_comp_isStronglyCartesian_ofArrows_eq` over the decomposition of
  `U`.

The source `(Sch/W)_{fppf}` is `CategoryTheory.Over.forget W`, whose fibres are *thin*: an object
of the fibre over `T` is an arrow `T ⟶ W` and there is at most one morphism over a given arrow of
the site (`CategoryTheory.Over.hom_ext_of_isHomLift`). That is what makes the last equation
cheap: after the three gluings it reduces to an equality of two morphisms of `Over W` lying over
one and the same arrow of the site, which thinness settles. The dictionary between objects of the
fibres and arrows of the site is `CategoryTheory.Over.fiberSec`, `CategoryTheory.Over.fiberOfSec`
and `CategoryTheory.Over.homOfFiberSec`.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u

-- The instance arguments of `CategoryTheory.Functor.IsHomLift` and
-- `CategoryTheory.Functor.IsStronglyCartesian` are only found after unfolding the inclusion of a
-- fibre into the total category, as recorded in
-- `StacksFrontier/CategoryTheory/FiberedCategory/ChoiceOfPullbacks.lean`.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The first-order lifting property of Stacks 06D0 descends from the summands to a
scheme-valued point out of a coproduct.** Let `𝒴` be a category fibred in groupoids over the big
fppf site of `S` which is a stack for the fppf topology, let the underlying scheme of `W` be the
coproduct of the underlying schemes of the `Z i` along `jj i`, and let `g` be a 1-morphism out of
the category represented by `W` whose restriction along each `jj i` is 2-isomorphic to `f i`. If
every `f i` solves every first-order lifting problem, so does `g`.

The lifting problem for `g` over a first-order thickening `tk : U ⟶ U'` of affine objects is cut
into finitely many lifting problems, one for each piece of the clopen decomposition of `U` that
the given arrow `U ⟶ W` induces, thickened to `U'` by
`AlgebraicGeometry.BigFppfOver.exists_thickened_decomposition_of_hom_coproduct`; the piecewise
solutions are then glued. -/
theorem hasFirstOrderObjectLifts_of_isColimit_of_forall
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    {I : Type u} (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeFibredCategory B S hS W ⟶ 𝒴)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hfg : ∀ i, Nonempty (schemeFibredCategoryMap B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, HasFirstOrderObjectLifts B S hS (f i)) :
    HasFirstOrderObjectLifts B S hS g := by
  classical
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : (schemeFibredCategory B S hS W).val.p.IsFibered :=
    (schemeFibredCategory B S hS W).isFiberedInGroupoids.isFibered
  -- the functor underlying `g`, read on the slice of the site over `W`
  let GW : Over W ⥤ 𝒴.val.obj := CatFiberedInGroupoids.homFunctor g
  have hGW : GW ⋙ 𝒴.val.p = Over.forget W := CatFiberedInGroupoids.homFunctor_comp_p g
  -- the image of a lift under `GW`, with the hypothesis explicit
  have hGlift : ∀ {T₁ T₂ : BigFppfOver B S hS} {c₁ c₂ : Over W} (fm : T₁ ⟶ T₂) (φ : c₁ ⟶ c₂),
      (Over.forget W).IsHomLift fm φ → 𝒴.val.p.IsHomLift fm (GW.map φ) := by
    intro _ _ _ _ fm φ hφ
    have := hφ
    exact Functor.isHomLift_map_of_comp_eq hGW fm φ
  have hGcart : ∀ {T₁ T₂ : BigFppfOver B S hS} {c₁ c₂ : Over W} (fm : T₁ ⟶ T₂) (φ : c₁ ⟶ c₂),
      (Over.forget W).IsHomLift fm φ → 𝒴.val.p.IsStronglyCartesian fm (GW.map φ) := by
    intro _ _ _ _ fm φ hφ
    have : (schemeFibredCategory B S hS W).val.p.IsHomLift fm φ := hφ
    exact CatFiberedInGroupoids.isStronglyCartesian_map g fm φ
  have hgi : ∀ i, HasFirstOrderObjectLifts B S hS
      (schemeFibredCategoryMap B S hS (jj i) ≫ g) := fun i =>
    hasFirstOrderObjectLifts_of_iso B S hS (hfg i).some.symm (hf i)
  let ee := (colimit.isColimit (Discrete.functor
    fun i => (BigFppfOver.toScheme B S hS).obj (Z i))).coconePointUniqueUpToIso hW
  have hee : ∀ i, Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (Z i)) i ≫ ee.hom =
      (BigFppfOver.toScheme B S hS).map (jj i) := fun i =>
    (colimit.isColimit (Discrete.functor
      fun i => (BigFppfOver.toScheme B S hS).obj (Z i))).comp_coconePointUniqueUpToIso_hom
      hW ⟨i⟩
  intro U U' tk hU hU' ht x y' a ha
  let xA : (Over.forget W).Fiber U := x
  obtain ⟨σ, hσ, k, Ua, Ua', p, q, ta, w, hUaAff, hUa'Aff, htaThick, htaSq, hwFac,
      hpImm, hpCov, hpDisj, hqImm, hqCov, hqDisj⟩ :=
    BigFppfOver.exists_thickened_decomposition_of_hom_coproduct jj ee hee tk hU hU' ht
      (Over.fiberSec xA)
  have hpSieve : Sieve.ofArrows Ua p ∈ BigFppfOver.topology B S hS U :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hpImm hpCov
  have hqSieve : Sieve.ofArrows Ua' q ∈ BigFppfOver.topology B S hS U' :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS q hqImm hqCov
  have hqMono : ∀ b, Mono (q b) := by
    intro b
    have := hqImm b
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hqBot : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ {Y : BigFppfOver B S hS} (u : Y ⟶ Ua' b₁)
      (v : Y ⟶ Ua' b₂), u ≫ q b₁ = v ≫ q b₂ →
      (⊥ : Sieve Y) ∈ BigFppfOver.topology B S hS Y := by
    intro b₁ b₂ hne Y u v huv
    refine BigFppfOver.bot_mem_topology Y ⟨fun y => ?_⟩
    have h1 : ((BigFppfOver.toScheme B S hS).map (q b₁))
          (((BigFppfOver.toScheme B S hS).map u) y) =
        ((BigFppfOver.toScheme B S hS).map (q b₂))
          (((BigFppfOver.toScheme B S hS).map v) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, huv]
    exact Set.disjoint_left.mp (hqDisj hne) ⟨_, rfl⟩ ⟨_, h1.symm⟩
  -- the two descriptions of the piece of `x` over `Ua b`, and their comparison
  let wb : ∀ b : σ, (Over.forget (Z (k b))).Fiber (Ua b) := fun b => Over.fiberOfSec (w b)
  let xb : ∀ b : σ, (Over.forget W).Fiber (Ua b) := fun b =>
    pullbackFiber (Over.forget W) xA (p b)
  let pb : ∀ b : σ, (Over.forget W).Fiber (Ua b) := fun b =>
    ⟨(Over.map (jj (k b))).obj (wb b).1, (wb b).2⟩
  have hsecxb : ∀ b, Over.fiberSec (xb b) = p b ≫ Over.fiberSec xA := fun b =>
    Over.fiberSec_pullbackFiber xA (p b)
  have hsecpb : ∀ b, Over.fiberSec (pb b) = p b ≫ Over.fiberSec xA := fun b =>
    (Over.fiberSec_fiberOfSec (w b ≫ jj (k b))).trans (hwFac b)
  let ηb : ∀ b : σ, (pb b).1 ⟶ (xb b).1 := fun b =>
    Over.homOfFiberSec (𝟙 (Ua b)) (by rw [hsecpb b, hsecxb b, Category.id_comp])
  let ηb' : ∀ b : σ, (xb b).1 ⟶ (pb b).1 := fun b =>
    Over.homOfFiberSec (𝟙 (Ua b)) (by rw [hsecpb b, hsecxb b, Category.id_comp])
  have hηblift : ∀ b, (Over.forget W).IsHomLift (𝟙 (Ua b)) (ηb b) := fun b =>
    Over.isHomLift_homOfFiberSec _ _
  have hηb'lift : ∀ b, (Over.forget W).IsHomLift (𝟙 (Ua b)) (ηb' b) := fun b =>
    Over.isHomLift_homOfFiberSec _ _
  have hηb : ∀ b, ηb' b ≫ ηb b = 𝟙 (xb b).1 := by
    intro b
    refine Over.hom_ext_of_isHomLift (𝟙 (Ua b)) ?_ ?_
    · have := hηb'lift b
      have := hηblift b
      infer_instance
    · exact (Over.isHomLift_forget_iff (𝟙 (xb b).1) (𝟙 (Ua b)) (xb b).2 (xb b).2).2 (by simp)
  -- the data of the lifting problem over a piece
  let ρb : ∀ b : σ, (xb b).1 ⟶ xA.1 := fun b => IsPreFibered.pullbackMap xA.2 (p b)
  have hρlift : ∀ b, (Over.forget W).IsHomLift (p b) (ρb b) := fun b =>
    (IsPreFibered.pullbackMap.IsCartesian xA.2 (p b)).toIsHomLift
  let yb : ∀ b : σ, 𝒴.val.p.Fiber (Ua' b) := fun b => pullbackFiber 𝒴.val.p y' (q b)
  let κb : ∀ b : σ, (yb b).1 ⟶ y'.1 := fun b => IsPreFibered.pullbackMap y'.2 (q b)
  have hκcart : ∀ b, 𝒴.val.p.IsStronglyCartesian (q b) (κb b) := by
    intro b
    have : 𝒴.val.p.IsCartesian (q b) (κb b) := IsPreFibered.pullbackMap.IsCartesian y'.2 (q b)
    infer_instance
  have hcomp₁ : ∀ b, 𝒴.val.p.IsHomLift (ta b ≫ q b)
      (GW.map (ηb b) ≫ GW.map (ρb b) ≫ a) := by
    intro b
    have := hGlift (p b) (ρb b) (hρlift b)
    have := hGlift (𝟙 (Ua b)) (ηb b) (hηblift b)
    have := ha
    rw [htaSq b]
    infer_instance
  -- the piecewise solutions
  have hstep : ∀ b : σ, ∃ (x'b : (Over.forget (Z (k b))).Fiber (Ua' b))
      (bbb : (wb b).1 ⟶ x'b.1)
      (cbb : GW.obj ((Over.map (jj (k b))).obj x'b.1) ⟶ (yb b).1),
      (Over.forget (Z (k b))).IsHomLift (ta b) bbb ∧
        𝒴.val.p.IsHomLift (𝟙 (Ua' b)) cbb ∧
        (GW.map ((Over.map (jj (k b))).map bbb) ≫ cbb) ≫ κb b =
          GW.map (ηb b) ≫ GW.map (ρb b) ≫ a := by
    intro b
    obtain ⟨τ, hτlift, hτfac⟩ : ∃ τ : GW.obj (pb b).1 ⟶ (yb b).1,
        𝒴.val.p.IsHomLift (ta b) τ ∧ τ ≫ κb b = GW.map (ηb b) ≫ GW.map (ρb b) ≫ a := by
      have := hcomp₁ b
      have := hκcart b
      exact (Functor.IsStronglyCartesian.universal_property 𝒴.val.p (q b)
        (κb b) (ta b) (ta b ≫ q b) rfl (GW.map (ηb b) ≫ GW.map (ρb b) ≫ a)).exists
    obtain ⟨x'b, bbb, cbb, hbbb, hcbb, hbcb⟩ :=
      hgi (k b) (Ua b) (Ua' b) (ta b) (hUaAff b) (hUa'Aff b) (htaThick b) (wb b) (yb b)
        τ hτlift
    exact ⟨x'b, bbb, cbb, hbbb, hcbb, (congrArg (· ≫ κb b) hbcb).trans hτfac⟩
  choose x' bbs cbs hbbs hcbs hbcs using hstep
  -- the glued arrow `U' ⟶ W`
  let sb : ∀ b : σ, Ua' b ⟶ W := fun b => Over.fiberSec (x' b) ≫ jj (k b)
  obtain ⟨xs, hxs, -⟩ := BigFppfOver.existsUnique_section_of_disjoint_openCover
    (BigFppfOver.isSheaf_of_type_yoneda_obj W) q hqImm hqCov hqDisj sb
  have hxs' : ∀ b, q b ≫ xs = sb b := hxs
  let X' : (Over.forget W).Fiber U' := Over.fiberOfSec xs
  have hsecX' : Over.fiberSec X' = xs := Over.fiberSec_fiberOfSec xs
  have hbbsec : ∀ b, ta b ≫ Over.fiberSec (x' b) = w b := fun b =>
    (Over.fiberSec_eq_of_isHomLift (ta b) (bbs b) (hbbs b)).symm.trans
      (Over.fiberSec_fiberOfSec (w b))
  have hlocsec : ∀ b, p b ≫ Over.fiberSec xA = ta b ≫ sb b := by
    intro b
    rw [← hwFac b, ← hbbsec b, Category.assoc]
  have hsecx : Over.fiberSec xA = tk ≫ Over.fiberSec X' := by
    rw [hsecX']
    refine BigFppfOver.section_ext_of_disjoint_openCover
      (BigFppfOver.isSheaf_of_type_yoneda_obj W) p hpImm hpCov hpDisj (fun b => ?_)
    show p b ≫ Over.fiberSec xA = p b ≫ tk ≫ xs
    rw [← Category.assoc, ← htaSq b, Category.assoc, hxs' b, ← hlocsec b]
  have hblift : (Over.forget W).IsHomLift tk (Over.homOfFiberSec tk hsecx) :=
    Over.isHomLift_homOfFiberSec _ _
  -- the pieces of the lifted object, and their comparisons
  let x'r : ∀ b : σ, (Over.forget W).Fiber (Ua' b) := fun b =>
    pullbackFiber (Over.forget W) X' (q b)
  let p'b : ∀ b : σ, (Over.forget W).Fiber (Ua' b) := fun b =>
    ⟨(Over.map (jj (k b))).obj (x' b).1, (x' b).2⟩
  let πb : ∀ b : σ, (x'r b).1 ⟶ X'.1 := fun b => IsPreFibered.pullbackMap X'.2 (q b)
  have hπlift : ∀ b, (Over.forget W).IsHomLift (q b) (πb b) := fun b =>
    (IsPreFibered.pullbackMap.IsCartesian X'.2 (q b)).toIsHomLift
  have hsecx'r : ∀ b, Over.fiberSec (x'r b) = sb b := fun b => by
    rw [Over.fiberSec_pullbackFiber X' (q b), hsecX', hxs' b]
  have hsecp'b : ∀ b, Over.fiberSec (p'b b) = sb b := fun b =>
    (Category.assoc (eqToHom (x' b).2.symm) (x' b).1.hom (jj (k b))).symm
  let η'b : ∀ b : σ, (x'r b).1 ⟶ (p'b b).1 := fun b =>
    Over.homOfFiberSec (𝟙 (Ua' b)) (by rw [hsecx'r b, hsecp'b b, Category.id_comp])
  let ζ'b : ∀ b : σ, (xb b).1 ⟶ (x'r b).1 := fun b =>
    Over.homOfFiberSec (ta b) (by rw [hsecxb b, hsecx'r b, hlocsec b])
  have hη'blift : ∀ b, (Over.forget W).IsHomLift (𝟙 (Ua' b)) (η'b b) := fun b =>
    Over.isHomLift_homOfFiberSec _ _
  have hζ'blift : ∀ b, (Over.forget W).IsHomLift (ta b) (ζ'b b) := fun b =>
    Over.isHomLift_homOfFiberSec _ _
  -- the glued vertical identification
  let Gx' : 𝒴.val.p.Fiber U' := (Fiber.mapOfComp (Over.forget W) 𝒴.val.p GW hGW U').obj X'
  let Gx'r : ∀ b : σ, 𝒴.val.p.Fiber (Ua' b) := fun b =>
    (Fiber.mapOfComp (Over.forget W) 𝒴.val.p GW hGW (Ua' b)).obj (x'r b)
  have hGXcart : ∀ b, 𝒴.val.p.IsCartesian (q b) (GW.map (πb b)) := by
    intro b
    have := hGcart (q b) (πb b) (hπlift b)
    infer_instance
  let Ib : ∀ b : σ, pullbackFiber 𝒴.val.p Gx' (q b) ≅ Gx'r b := fun b =>
    fiberIsoOfCartesian (q b) (IsPreFibered.pullbackMap Gx'.2 (q b)) (GW.map (πb b))
      (IsPreFibered.pullbackMap.IsCartesian _ _) (hGXcart b)
  have hνlift : ∀ b, 𝒴.val.p.IsHomLift (𝟙 (Ua' b)) (GW.map (η'b b) ≫ cbs b) := by
    intro b
    have := hGlift (𝟙 (Ua' b)) (η'b b) (hη'blift b)
    have := hcbs b
    infer_instance
  let mb : ∀ b : σ, pullbackFiber 𝒴.val.p Gx' (q b) ⟶ yb b := fun b =>
    (Ib b).hom ≫ (⟨GW.map (η'b b) ≫ cbs b, hνlift b⟩ : Gx'r b ⟶ yb b)
  obtain ⟨c₀, hc₀⟩ := Functor.exists_fiberHom_of_disjointCover 𝒴.val.p
    (h𝒴.isMorSheaf U' Gx' y') Ua' q hqMono hqSieve hqBot mb
  -- the restriction of the glued identification to a piece
  have hrestr : ∀ b, GW.map (η'b b) ≫ cbs b ≫ κb b =
      GW.map (πb b) ≫ Fiber.fiberInclusion.map c₀ := by
    intro b
    have h1 : Fiber.fiberInclusion.map (mb b) ≫ κb b =
        IsPreFibered.pullbackMap Gx'.2 (q b) ≫ Fiber.fiberInclusion.map c₀ := by
      have h0 := Functor.pullbackFiberHom_fac c₀ (q b)
      rw [hc₀ b] at h0
      exact h0
    have h2 : Fiber.fiberInclusion.map ((Ib b).hom) ≫ GW.map (πb b) =
        IsPreFibered.pullbackMap Gx'.2 (q b) :=
      fiberIsoOfCartesian_hom_fac (q b) _ _ _ _
    have h5 : Fiber.fiberInclusion.map (mb b) =
        Fiber.fiberInclusion.map ((Ib b).hom) ≫ (GW.map (η'b b) ≫ cbs b) :=
      Fiber.fiberInclusion.map_comp ((Ib b).hom)
        (⟨GW.map (η'b b) ≫ cbs b, hνlift b⟩ : Gx'r b ⟶ yb b)
    refine (cancel_epi (Fiber.fiberInclusion.map ((Ib b).hom))).mp ?_
    erw [← Category.assoc (GW.map (η'b b)), ← Category.assoc (Fiber.fiberInclusion.map _),
      ← h5, h1, ← h2, Category.assoc]
    rfl
  -- the morphism to the lifted object, restricted to a piece
  have hpiece : ∀ b, ρb b ≫ Over.homOfFiberSec tk hsecx = ζ'b b ≫ πb b := by
    intro b
    have := hρlift b
    have := hblift
    have := hζ'blift b
    have := hπlift b
    refine Over.hom_ext_of_isHomLift (p b ≫ tk) inferInstance ?_
    rw [← htaSq b]
    infer_instance
  -- the key equality of two morphisms of `Over W` over one and the same arrow of the site
  have hkey : ∀ b, ζ'b b ≫ η'b b = ηb' b ≫ (Over.map (jj (k b))).map (bbs b) := by
    intro b
    have hbm : (Over.forget W).IsHomLift (ta b) ((Over.map (jj (k b))).map (bbs b)) :=
      (Over.isHomLift_forget_iff ((Over.map (jj (k b))).map (bbs b)) (ta b)
          (wb b).2 (x' b).2).2
        ((Over.isHomLift_forget_iff (bbs b) (ta b) (wb b).2 (x' b).2).1 (hbbs b))
    refine Over.hom_ext_of_isHomLift (ta b) ?_ ?_
    · have := hζ'blift b
      have := hη'blift b
      infer_instance
    · have := hηb'lift b
      have := hbm
      infer_instance
  -- the compatibility equation, checked over the decomposition of `U`
  refine ⟨X', Over.homOfFiberSec tk hsecx, Fiber.fiberInclusion.map c₀, hblift, c₀.2, ?_⟩
  have hφlift : 𝒴.val.p.IsHomLift tk
      (GW.map (Over.homOfFiberSec tk hsecx) ≫ Fiber.fiberInclusion.map c₀) := by
    simpa using @IsHomLift.comp _ _ _ _ 𝒴.val.p _ _ _ _ _ _ tk (𝟙 U')
      (GW.map (Over.homOfFiberSec tk hsecx)) (Fiber.fiberInclusion.map c₀)
      (hGlift tk (Over.homOfFiberSec tk hsecx) hblift) c₀.2
  show GW.map (Over.homOfFiberSec tk hsecx) ≫ Fiber.fiberInclusion.map c₀ = a
  refine Functor.eq_of_comp_isStronglyCartesian_ofArrows_eq 𝒴.val.p tk
    (h𝒴.isMorSheaf U ((Fiber.mapOfComp (Over.forget W) 𝒴.val.p GW hGW U).obj xA)
      (pullbackFiber 𝒴.val.p y' tk))
    Ua p hpSieve (fun b => GW.map (ρb b))
    (fun b => hGcart (p b) (ρb b) (hρlift b)) hφlift ha (fun b => ?_)
  erw [← Category.assoc (GW.map (ρb b)), ← GW.map_comp, hpiece b, GW.map_comp,
    Category.assoc (GW.map (ζ'b b)), ← hrestr b, ← Category.assoc (GW.map (ζ'b b)),
    ← GW.map_comp, hkey b, GW.map_comp, Category.assoc (GW.map (ηb' b)),
    ← Category.assoc (GW.map ((Over.map (jj (k b))).map (bbs b))), hbcs b,
    ← Category.assoc (GW.map (ηb' b)), ← GW.map_comp, hηb b, GW.map_id, Category.id_comp]
  rfl

/-- **Stacks 06D0 descends from the summands to a scheme-valued point out of a coproduct.** Let
`𝒴` be a category fibred in groupoids over the big fppf site of `S` which is a stack for the fppf
topology, let the underlying scheme of `W` be the coproduct of the underlying schemes of the
`Z i` along `jj i`, and let `g` be a 1-morphism out of the category represented by `W` whose
restriction along each `jj i` is 2-isomorphic to `f i`. If every `f i` is formally smooth on
objects, so is `g`. -/
theorem isFormallySmoothOnObjects_of_isColimit_of_forall
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    {I : Type u} (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeFibredCategory B S hS W ⟶ 𝒴)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hfg : ∀ i, Nonempty (schemeFibredCategoryMap B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i)) :
    IsFormallySmoothOnObjects B S hS (schemeFibredCategory B S hS W) 𝒴 g :=
  isFormallySmoothOnObjects_of_exists_homLift B S hS g
    (hasFirstOrderObjectLifts_of_isColimit_of_forall B S hS h𝒴 Z W jj hW g f hfg
      fun i => exists_homLift_of_isFormallySmoothOnObjects B S hS (f i) (hf i))

end AlgebraicGeometry.Stack

end
