module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
import StacksFrontier.AlgebraicGeometry.Size.OpenCover
import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated

/-!
# Scheme models at a stage of an étale scheme over a limit of algebraic spaces

Let `X = lim X_i` be a directed inverse limit of quasi-compact and quasi-separated algebraic
spaces with affine transition morphisms, over the terminal scheme of a big fppf site whose
size cutoff has cofinality larger than the index set, and let `W → X` be an étale morphism
from a quasi-compact quasi-separated scheme `W` of the site. Then for some stage `i₀` there
are schemes `W_i` (`i ≥ i₀`) of the site, étale over `X_i`, with `W_i = W_{i'} ×_{X_{i'}} X_i`
for `i ≥ i'` and `W = W_i ×_{X_i} X`; the transition morphisms `W_i → W_{i'}` are affine
morphisms of schemes, every `W_i` is quasi-compact and quasi-separated, and `W` is the limit
of the `W_i` as a scheme. These are the steps (b) and (c) of the proof of Stacks 07SU.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_isLimit_of_isAffineHom`: a limit of a cofiltered
  system of schemes of a big fppf site with affine transition morphisms, indexed by a category
  small for the cofinality of the size cutoff, lies again in the site.
* `AlgebraicGeometry.Space.isLimitToSchemeMapConeOfIsLimitYoneda`: over the
  terminal scheme, a cone of the site over such a system whose image under Yoneda is a limit
  of presheaves is a limit of schemes.
* `AlgebraicGeometry.Space.exists_etale_scheme_models`: the scheme models `W_i`.

## Implementation notes

The source descends `W → X`, a morphism of finite presentation, to a stage by Stacks 07SK,
makes it étale at a later stage by Stacks 07SL, and makes the base changes `W_i` schemes at a
later stage by Stacks 07SR. Here the base changes `W_i` are the stages of the descent
situation `AlgebraicGeometry.Space.MorphismDescentSystem.stagesSourceDescentSituation` built
on the morphism given by Stacks 07SK; its limit is `W`, so Stacks 07SR applies to it. The
representing objects of the stages beyond the chosen one are assembled into a functor with
`CategoryTheory.Functor.essImage.liftFunctor`.

That `W` is the limit of the `W_i` as a scheme, and not only as a presheaf on the site, uses
that the limit scheme of the `W_i`, which exists because the transition morphisms are affine,
is small enough to lie in the site: over the terminal scheme every morphism of schemes
between objects of the site is a morphism of the site, so the presheaf-level universal
property then identifies it with `W`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
-/

public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry

/-- **A cofiltered limit of schemes of a big fppf site with affine transition morphisms lies
in the site**, provided the index category has fewer objects, and fewer morphisms between any
two objects, than the cofinality of the size cutoff.

Over a fixed stage `k₀`, the limit is covered by the inverse images of the affine opens `U`
of `D k₀`, of which there are fewer than the cutoff; each of them is the limit of the affine
inverse images of `U` in the stages over `k₀`, whose sizes are bounded by the supremum of the
sizes of the stages, uniformly in `U`. -/
theorem BigFppfSite.contains_of_isLimit_of_isAffineHom (B : BigFppfSite.{u}) {J : Type u}
    [SmallCategory J] [IsCofiltered J] (hJ : #J < B.cutoff.ord.cof)
    (hJhom : ∀ a b : J, #(a ⟶ b) < B.cutoff.ord.cof) (G : J ⥤ Scheme.{u})
    [∀ {a b : J} (g : a ⟶ b), IsAffineHom (G.map g)] (hG : ∀ j, B.Contains (G.obj j))
    {c : Cone G} (hc : IsLimit c) : B.Contains c.pt := by
  obtain ⟨k₀⟩ := IsCofiltered.nonempty (C := J)
  have hJ' : #(Over k₀) < B.cutoff.ord.cof := mk_over_lt B.aleph0_lt_cutoff_cof hJ hJhom k₀
  set ν : Cardinal.{u} := ⨆ j : J, (G.obj j).size
  have hνlt : ν < B.cutoff := Cardinal.iSup_lt_of_lt_cof_ord hJ hG
  have hpreim : ∀ U : (G.obj k₀).affineOpens,
      (↑(c.π.app k₀ ⁻¹ᵁ U.1) : Scheme.{u}).size ≤ max ℵ₀ (#(Over k₀) * ν) := by
    intro U
    have haff : ∀ j : Over k₀, IsAffine ((opensDiagram G k₀ U.1).obj j) := fun j =>
      U.2.preimage (G.map j.hom)
    have hsize : ∀ j : Over k₀, ((opensDiagram G k₀ U.1).obj j).size ≤ ν := fun j =>
      (Scheme.size_coe_opens_le (G.obj j.left) (G.map j.hom ⁻¹ᵁ U.1)).trans
        (le_ciSup Cardinal.bddAbove_of_small j.left)
    have hlim := Scheme.size_le_of_isLimit_of_isAffine _ haff hsize
      (isLimitOpensCone G c hc k₀ U.1)
    rwa [opensCone_pt] at hlim
  have hcov : (⨆ U : (G.obj k₀).affineOpens, c.π.app k₀ ⁻¹ᵁ U.1) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (c.π.app k₀).base x ∈ (⊤ : (G.obj k₀).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hx
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
  have _ : Nonempty (G.obj k₀).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  have hbound := Scheme.size_le_of_iSup_eq_top
    (fun U : (G.obj k₀).affineOpens => c.π.app k₀ ⁻¹ᵁ U.1) hcov
  refine lt_of_le_of_lt hbound (max_lt ((G.obj k₀).mk_affineOpens_le_size.trans_lt (hG k₀))
    ((ciSup_le' hpreim).trans_lt ?_))
  exact max_lt B.aleph0_lt_cutoff (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le
    (hJ'.trans_le (Ordinal.cof_ord_le _)) hνlt)

namespace Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A limit of representable presheaves is a limit of schemes.** Over the terminal scheme,
let `F` be a cofiltered system of objects of the site whose underlying schemes have affine
transition morphisms, indexed by a category small for the cofinality of the size cutoff. A
cone over `F` whose image under Yoneda is a limit of presheaves is a limit of the underlying
schemes.

The limit scheme of the system exists and lies in the site
(`AlgebraicGeometry.BigFppfSite.contains_of_isLimit_of_isAffineHom`); every morphism of
schemes between objects of the site over the terminal scheme is a morphism of the site, so
the limit scheme is a cone of the site over `F`, and the two universal properties give
mutually inverse morphisms between it and the vertex of the given cone. -/
noncomputable def isLimitToSchemeMapConeOfIsLimitYoneda {J : Type u} [SmallCategory J]
    [IsCofiltered J] (hJ : #J < B.cutoff.ord.cof)
    (hJhom : ∀ a b : J, #(a ⟶ b) < B.cutoff.ord.cof)
    (F : J ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hF : ∀ {a b : J} (g : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (F.map g)))
    (c : Cone F) (hc : IsLimit (yoneda.mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone c) := by
  let T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  let G := F ⋙ T
  have _ : ∀ {a b : J} (g : a ⟶ b), _root_.AlgebraicGeometry.IsAffineHom (G.map g) := hF
  have hL : B.Contains (limit G) := B.contains_of_isLimit_of_isAffineHom hJ hJhom G
    (fun j => (F.obj j).left.property) (limit.isLimit G)
  -- every morphism of schemes between objects of the site over the terminal scheme is a
  -- morphism of the site
  let lft : ∀ {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}, (T.obj X ⟶ T.obj Y) → (X ⟶ Y) :=
    fun f => Over.homMk ⟨f⟩ (ObjectProperty.hom_ext _ (terminal.hom_ext _ _))
  have hlft : ∀ {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ} (f : T.obj X ⟶ T.obj Y),
      T.map (lft f) = f := fun _ => rfl
  -- the limit scheme, as an object of the site, and its cone over `F`
  let L : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    Over.mk (X := B.obj hZ) (Y := ⟨limit G, hL⟩) ⟨terminal.from _⟩
  let cL : Cone F :=
    { pt := L
      π :=
        { app := fun j => lft (limit.π G j)
          naturality := fun a b g => by
            apply T.map_injective
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.map_comp, hlft]
            exact (limit.w G g).symm } }
  have hcS : IsLimit c := isLimitOfReflects yoneda hc
  let t : L ⟶ c.pt := hcS.lift cL
  have ht : ∀ j, t ≫ c.π.app j = lft (X := L) (Y := F.obj j) (limit.π G j) := hcS.fac cL
  let s : T.obj c.pt ⟶ limit G := (limit.isLimit G).lift (T.mapCone c)
  have hs : ∀ j, s ≫ limit.π G j = T.map (c.π.app j) := (limit.isLimit G).fac (T.mapCone c)
  have h₁ : T.map t ≫ s = 𝟙 _ := by
    refine limit.hom_ext fun j => ?_
    rw [Category.assoc, hs, ← T.map_comp, ht, hlft, Category.id_comp]
  have h₂ : s ≫ T.map t = 𝟙 _ := by
    have h : lft (X := c.pt) (Y := L) s ≫ t = 𝟙 c.pt := by
      refine hcS.hom_ext fun j => ?_
      rw [Category.assoc, ht, Category.id_comp]
      apply T.map_injective
      rw [T.map_comp, hlft, hlft]
      exact hs j
    have h' := congrArg T.map h
    rwa [T.map_comp, hlft, T.map_id] at h'
  have _ : IsIso s := ⟨⟨T.map t, h₂, h₁⟩⟩
  exact IsLimit.ofPointIso (limit.isLimit G)

/-- Étaleness of a morphism of algebraic spaces is stable under base change: the bundled form
`AlgebraicGeometry.Space.isEtale_of_isPullback`, for a cartesian square of presheaves whose
four corners are algebraic spaces. -/
private theorem isEtale_of_isPullback_of_isAlgebraicSpace {S : Scheme.{u}} {hS : B.Contains S}
    {X' X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hZ' : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) {p : X' ⟶ X} {f' : X' ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback p f' f g) (hf : IsEtale B S hS f) : IsEtale B S hS f' := by
  let P : ObjectProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := IsAlgebraicSpace B S hS
  let X'' : P.FullSubcategory := ⟨X', hX'⟩
  let X''' : P.FullSubcategory := ⟨X, hX⟩
  let Z'' : P.FullSubcategory := ⟨Z, hZ'⟩
  let Y'' : P.FullSubcategory := ⟨Y, hY⟩
  have h' : IsPullback (ObjectProperty.homMk p : X'' ⟶ X''')
      (ObjectProperty.homMk f' : X'' ⟶ Z'') (ObjectProperty.homMk f : X''' ⟶ Y'')
      (ObjectProperty.homMk g : Z'' ⟶ Y'') :=
    IsPullback.of_map P.ι (ObjectProperty.hom_ext _ h.w) h
  exact isEtale_of_isPullback B S hS _ _ _ _ h' hf

/-- The size hypotheses on the index category `Iᵒᵖ`, from the size of the preorder `I`. -/
private theorem mk_op_lt_and_mk_hom_lt {I : Type u} [Preorder I]
    (hI : #I < B.cutoff.ord.cof) :
    #(Iᵒᵖ) < B.cutoff.ord.cof ∧ ∀ a b : Iᵒᵖ, #(a ⟶ b) < B.cutoff.ord.cof :=
  ⟨by rwa [← Cardinal.mk_congr (Opposite.equivToOpposite (α := I))], fun a b =>
    (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)⟩

/-- **Scheme models of an étale scheme over a limit, from one stage on.** If the étale
scheme `W → U = lim D` is already the base change of an étale morphism `t : T₁ → D_{i₀}` from a
quasi-compact quasi-separated scheme `T₁` of the site, its base changes `W_k = T₁ ×_{D_{i₀}} D_k`
for `k ≥ i₀` are the scheme models: each is represented, because the transition morphism
`D_k → D_{i₀}` is affine (Stacks 03WG), and its projection to `T₁` is an affine morphism of
schemes. -/
private theorem exists_etale_scheme_models_of_stage {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (hI : #I < B.cutoff.ord.cof)
    (D : Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj i))
    (hA : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B (⊤_ Scheme.{u}) hZ (D.map g))
    {U : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (π : (Functor.const Iᵒᵖ).obj U ⟶ D)
    (hπ : IsLimit (Cone.mk U π)) {W : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (w : yoneda.obj W ⟶ U) (i₀ : I) (T₁ : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T₁)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T₁)]
    (t : yoneda.obj T₁ ⟶ D.obj (op i₀))
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf t) (a : W ⟶ T₁)
    (ha : IsPullback (yoneda.map a) w t (π.app (op i₀))) :
    ∃ (Ws : {i : I // i₀ ≤ i}ᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (ws : Ws ⋙ yoneda ⟶ (Subtype.mono_coe (fun i : I => i₀ ≤ i)).functor.op ⋙ D)
      (πW : (Functor.const {i : I // i₀ ≤ i}ᵒᵖ).obj W ⟶ Ws),
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf (ws.app i)) ∧
      (∀ {a b : {i : I // i₀ ≤ i}ᵒᵖ} (g : a ⟶ b),
        IsPullback (yoneda.map (Ws.map g)) (ws.app a) (ws.app b)
          (((Subtype.mono_coe (fun i : I => i₀ ≤ i)).functor.op ⋙ D).map g)) ∧
      (∀ i : {i : I // i₀ ≤ i}ᵒᵖ,
        IsPullback (yoneda.map (πW.app i)) w (ws.app i) (π.app (op i.unop.1))) ∧
      (∀ {a b : {i : I // i₀ ≤ i}ᵒᵖ} (g : a ⟶ b),
        _root_.AlgebraicGeometry.IsAffineHom
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Ws.map g))) ∧
      (∀ i, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj i)) ∧
        QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj i))) ∧
      Nonempty (IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
        (Cone.mk W πW))) := by
  classical
  let T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let _ : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let J := {k : I // i₀ ≤ k}
  have _ : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let ι : J ⥤ I := (Subtype.mono_coe (fun k : I => i₀ ≤ k)).functor
  have _ : ι.Final := (Monotone.final_functor_iff (Subtype.mono_coe fun k : I => i₀ ≤ k)).2
    fun k => by
      obtain ⟨m, h₀, hk⟩ := exists_ge_ge i₀ k
      exact ⟨⟨m, h₀⟩, hk⟩
  let Dres := ι.op ⋙ D
  -- the transition morphisms to the stage `i₀`
  let tn : Dres ⟶ (Functor.const Jᵒᵖ).obj (D.obj (op i₀)) :=
    { app := fun k => D.map (homOfLE k.unop.2).op
      naturality := fun a b g => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Dres,
          Functor.comp_map]
        rw [← D.map_comp]
        exact congrArg D.map (Subsingleton.elim _ _) }
  -- the base changes of `t` to the stages, with their projections and cones
  let E := baseChangeOverSystem B _ hZ Dres tn t
  let σ : E ⟶ Dres := baseChangeOverProj B _ hZ Dres tn t
  let c : Cone Dres := (Cone.mk U π).whisker ι.op
  have hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv ι.op (Cone.mk U π)).symm hπ
  have hcg : ∀ k, c.π.app k ≫ tn.app k = π.app (op i₀) := fun k => by
    have h := π.naturality (homOfLE k.unop.2).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h
    exact h.symm
  let cE := baseChangeOverCone B _ hZ Dres tn t c (π.app (op i₀)) hcg
  have hcE : IsLimit cE := isLimit_baseChangeOverCone B _ hZ Dres tn t c _ hcg hc
  -- every base change is represented, by Stacks 03WG for the affine transition morphisms
  have hAff : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (D.map g) := fun _ =>
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B _ hZ (hD _) (hD _) (hA _)).2
  have hrel : ∀ k : Jᵒᵖ, (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (tn.app k) := fun _ => hAff _
  have hess : ∀ k, yoneda.essImage (E.obj k) := fun k =>
    ⟨(hrel k).rep.pullback t, ⟨((hrel k).rep.isPullback t).isoPullback⟩⟩
  let Ws := Functor.essImage.liftFunctor E (yoneda (C := BigFppfOver B (⊤_ Scheme.{u}) hZ)) hess
  let hiso : Ws ⋙ yoneda ≅ E :=
    Functor.essImage.liftFunctorCompIso E (yoneda (C := BigFppfOver B (⊤_ Scheme.{u}) hZ)) hess
  let ws : Ws ⋙ yoneda ⟶ Dres := hiso.hom ≫ σ
  let ew : yoneda.obj W ≅ pullback (π.app (op i₀)) t := ha.flip.isoPullback
  let legs : ∀ k, pullback (π.app (op i₀)) t ⟶ E.obj k := fun k => cE.π.app k
  have hlegs : ∀ {a b : Jᵒᵖ} (g : a ⟶ b), legs a ≫ E.map g = legs b := fun g =>
    (cE.w g)
  let πW : (Functor.const Jᵒᵖ).obj W ⟶ Ws :=
    { app := fun k => yoneda.preimage (ew.hom ≫ legs k ≫ hiso.inv.app k)
      naturality := fun a b g => by
        apply yoneda.map_injective
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.map_comp, Functor.map_preimage, Category.assoc]
        have h₁ : hiso.inv.app a ≫ yoneda.map (Ws.map g) = E.map g ≫ hiso.inv.app b :=
          (hiso.inv.naturality g).symm
        rw [h₁, ← Category.assoc (legs a), hlegs g] }
  -- the cartesian squares
  have hT : ∀ {a b : Jᵒᵖ} (g : a ⟶ b), IsPullback (E.map g) (σ.app a) (σ.app b) (Dres.map g) :=
    fun {a b} g => isPullback_baseChangeOverMap B _ hZ (tn.app a) (tn.app b) (Dres.map g)
      ((tn.naturality g).trans (Category.comp_id _)) t
  have hW : ∀ {a b : Jᵒᵖ} (g : a ⟶ b),
      IsPullback (yoneda.map (Ws.map g)) (ws.app a) (ws.app b) (Dres.map g) := by
    intro a b g
    refine (hT g).of_iso (hiso.app a).symm (hiso.app b).symm (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact hiso.inv.naturality g
    · simp [ws]
    · simp [ws]
    · simp
  have hC : ∀ k : Jᵒᵖ, IsPullback (legs k) (pullback.fst (π.app (op i₀)) t) (σ.app k)
      (c.π.app k) := fun k =>
    isPullback_baseChangeOverMap B _ hZ (π.app (op i₀)) (tn.app k) (c.π.app k) (hcg k) t
  have hUsq : ∀ k : Jᵒᵖ,
      IsPullback (yoneda.map (πW.app k)) w (ws.app k) (π.app (op k.unop.1)) := by
    intro k
    refine (hC k).of_iso ew.symm (hiso.app k).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [πW]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
      exact ha.flip.isoPullback_hom_fst
    · simp [ws]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  -- the projections to `T₁`, which are affine morphisms of schemes
  have hproj : ∀ k : Jᵒᵖ, ∃ pk : Ws.obj k ⟶ T₁,
      _root_.AlgebraicGeometry.IsAffineHom (T.map pk) := fun k => by
    let ek : yoneda.obj (Ws.obj k) ≅ pullback (tn.app k) t := hiso.app k
    let pk : Ws.obj k ⟶ T₁ := yoneda.preimage (ek.hom ≫ pullback.snd (tn.app k) t)
    have hpk : yoneda.map pk = ek.hom ≫ pullback.snd (tn.app k) t := yoneda.map_preimage _
    have hsq : IsPullback (ek.hom ≫ pullback.fst (tn.app k) t) (yoneda.map pk) (tn.app k) t :=
      IsPullback.of_iso_pullback
        ⟨by rw [hpk, Category.assoc, Category.assoc, pullback.condition]⟩ ek rfl hpk.symm
    exact ⟨pk, (hrel k).property t _ pk hsq⟩
  refine ⟨Ws, ws, πW, fun k => ?_, hW, hUsq, fun g => ?_, fun k => ?_, ⟨?_⟩⟩
  · -- étale: a base change of `t`
    have h : P.presheaf (σ.app k) :=
      P.presheaf.of_isPullback (IsPullback.of_hasPullback (tn.app k) t).flip ht
    exact MorphismProperty.RespectsIso.precomp _ (hiso.hom.app k) _ h
  · exact (hAff _).property (ws.app _) (ws.app _) (Ws.map g) (hW g).flip
  · obtain ⟨pk, hpk⟩ := hproj k
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (T.map pk),
      quasiSeparatedSpace_of_quasiSeparated (T.map pk)⟩
  · -- the scheme limit
    obtain ⟨hJ, hJhom⟩ := mk_op_lt_and_mk_hom_lt B (I := J) ((mk_subtype_le _).trans_lt hI)
    have h₁ : IsLimit ((Cone.postcompose hiso.hom).obj (yoneda.mapCone (Cone.mk W πW))) :=
      hcE.ofIsoLimit (Cones.ext ew (fun k => by simp [πW]; rfl)).symm
    exact isLimitToSchemeMapConeOfIsLimitYoneda B hZ hJ hJhom Ws
      (fun g => (hAff _).property (ws.app _) (ws.app _) (Ws.map g) (hW g).flip)
      (Cone.mk W πW) ((IsLimit.postcomposeHomEquiv hiso _) h₁)

/-- **Scheme models at a stage of an étale scheme over a limit** (steps (b) and (c) of the
proof of Stacks 07SU). Let `D` be a directed inverse system of quasi-compact and
quasi-separated algebraic spaces over the terminal scheme with affine transition morphisms,
indexed by a set smaller than the cofinality of the size cutoff of the site, with limit `U`,
and let `w : W → U` be étale with `W` a quasi-compact quasi-separated scheme of the site.
Then for some index `i₀` there are schemes `W_i` (`i ≥ i₀`) of the site and étale morphisms
`W_i → D_i` such that every transition square `W_i → W_{i'}` over `D_i → D_{i'}` and every
square `W → W_i` over `U → D_i` is cartesian; moreover the transition morphisms are affine
morphisms of schemes, every `W_i` is quasi-compact and quasi-separated, and `W` is the limit of
the `W_i` as a scheme.

`W → U` is of finite presentation, so Stacks 07SK descends it to a morphism `Y → D_i` of finite
presentation at some stage. Stacks 07SL makes its base change to some stage `j` étale. Its base
changes `Y_k` to the stages `k ≥ i` form a descent situation whose limit is `W`, a scheme, so by
Stacks 07SR some `Y_{k₁}` is a scheme, and then so is every `Y_k` with `k ≥ k₁`, the transition
morphism `Y_k → Y_{k₁}` being affine. The stage `i₀` is any common upper bound of `j` and
`k₁`. -/
theorem exists_etale_scheme_models {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (hI : #I < B.cutoff.ord.cof)
    (D : Iᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.obj i))
    (hA : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B (⊤_ Scheme.{u}) hZ (D.map g))
    {U : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (π : (Functor.const Iᵒᵖ).obj U ⟶ D)
    (hπ : IsLimit (Cone.mk U π)) {W : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W)]
    (w : yoneda.obj W ⟶ U)
    (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf w) :
    ∃ (i₀ : I) (Ws : {i : I // i₀ ≤ i}ᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (ws : Ws ⋙ yoneda ⟶ (Subtype.mono_coe (fun i : I => i₀ ≤ i)).functor.op ⋙ D)
      (πW : (Functor.const {i : I // i₀ ≤ i}ᵒᵖ).obj W ⟶ Ws),
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf (ws.app i)) ∧
      (∀ {a b : {i : I // i₀ ≤ i}ᵒᵖ} (g : a ⟶ b),
        IsPullback (yoneda.map (Ws.map g)) (ws.app a) (ws.app b)
          (((Subtype.mono_coe (fun i : I => i₀ ≤ i)).functor.op ⋙ D).map g)) ∧
      (∀ i : {i : I // i₀ ≤ i}ᵒᵖ,
        IsPullback (yoneda.map (πW.app i)) w (ws.app i) (π.app (op i.unop.1))) ∧
      (∀ {a b : {i : I // i₀ ≤ i}ᵒᵖ} (g : a ⟶ b),
        _root_.AlgebraicGeometry.IsAffineHom
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Ws.map g))) ∧
      (∀ i, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj i)) ∧
        QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj i))) ∧
      Nonempty (IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone
        (Cone.mk W πW))) := by
  classical
  let T := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  obtain ⟨hIop, hHomOp⟩ := mk_op_lt_and_mk_hom_lt B hI
  -- the limit, its comparison with `U`, and its separation properties
  let eU : U ≅ limit D := hπ.conePointUniqueUpToIso (limit.isLimit D)
  have heU : ∀ j, eU.hom ≫ limit.π D j = π.app j := fun j =>
    hπ.conePointUniqueUpToIso_hom_comp (limit.isLimit D) j
  have hL : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit D) :=
    isAlgebraicSpace_limit B _ hZ D hIop hHomOp hD hA
  obtain ⟨i₁⟩ := ‹Nonempty I›
  have hLqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (limit D) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hL (hqs (op i₁))
      (isQuasiSeparated_of_isAffineHom B _ hZ _ hL (hD _)
        (isAffineHom_limitπ B _ hZ D hIop hHomOp hA (op i₁)))
  have hWalg := isAlgebraicSpace_yoneda B _ hZ W
  have hWqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (yoneda.obj W) :=
    isQuasiCompact_yoneda_of_compact B _ hZ W inferInstance
  have hWqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (yoneda.obj W) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ (yoneda.obj W) hZ
      ⟨W, inferInstance, ⟨Functor.RepresentableBy.yoneda W⟩⟩
  -- Stacks 07SK: `W → lim D` descends to a stage
  have hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      T).presheaf (w ≫ eU.hom) := MorphismProperty.RespectsIso.postcomp _ eU.hom w hw
  have hFp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (w ≫ eU.hom) :=
    ⟨isLocallyOfFinitePresentation_of_presheafEtale B _ hZ hwe,
      isQuasiCompact_of_isQuasiCompactSpace B _ hZ hZ hL hLqs hWqc _,
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B _ hZ hZ hWalg hWqs _⟩
  obtain ⟨⟨i⟩, Yi, hYialg, hYifp, ⟨eY⟩⟩ := exists_model_of_finitePresentation B _ hZ hZ D
    hIop hHomOp hD hA hqc hqs (Over.mk (w ≫ eU.hom)) hWalg hFp
  have hYiqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Yi.left :=
    isQuasiCompactSpace_source_of_isQuasiCompact B _ hZ (hD _) (hqc _) hYifp.2.1
  have hYiqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Yi.left :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hYialg (hqs _) hYifp.2.2
  -- the morphism descent system of Stacks 084W on `Yi → D_i`
  let M : MorphismDescentSystem B (⊤_ Scheme.{u}) hZ hZ I :=
    { base := D
      indexSize := hI
      base_isAlgebraicSpace := fun j => hD (op j)
      transition_affine := hA
      limit_isAlgebraicSpace := hL
      initial := i
      source₀ := Yi.left
      target₀ := D.obj (op i)
      sourceToBase := Yi.hom
      targetToBase := 𝟙 _
      map₀ := Yi.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hYialg
      target₀_isAlgebraicSpace := hD _
      base₀_quasiCompact := hqc _
      base₀_quasiSeparated := hqs _
      source₀_quasiCompact := hYiqc
      source₀_quasiSeparated := hYiqs
      target₀_quasiCompact := hqc _
      target₀_quasiSeparated := hqs _ }
  -- its source over the limit is `W`
  let e0 : yoneda.obj W ≅ pullback (limit.π D (op i)) Yi.hom :=
    (Over.forget _).mapIso eY ≪≫ pullbackSymmetry _ _
  have he0 : e0.hom ≫ pullback.fst (limit.π D (op i)) Yi.hom = w ≫ eU.hom := by
    have h1 : eY.hom.left ≫ pullback.snd Yi.hom (limit.π D (op i)) = w ≫ eU.hom :=
      Over.w eY.hom
    calc e0.hom ≫ pullback.fst (limit.π D (op i)) Yi.hom
        = eY.hom.left ≫ ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) := Category.assoc _ _ _
      _ = w ≫ eU.hom := by rw [pullbackSymmetry_hom_comp_fst]; exact h1
  -- Stacks 07SL: the base change to some stage `j` is étale
  have hfstLim : IsEtale B (⊤_ Scheme.{u}) hZ (pullback.fst (limit.π D (op i)) Yi.hom) := by
    have h : pullback.fst (limit.π D (op i)) Yi.hom = e0.inv ≫ w ≫ eU.hom := by
      rw [← he0]; simp
    rw [h]
    exact isEtale_comp B _ hZ (isEtale_of_iso B _ hZ e0.symm)
      (isEtale_comp B _ hZ (isEtale_of_presheaf_etale B _ hZ hw) (isEtale_of_iso B _ hZ eU))
  have hmapLim : IsEtale B (⊤_ Scheme.{u}) hZ M.mapLimit := by
    have _ : IsIso (pullback.fst (limit.π D (op i)) (𝟙 (D.obj (op i)))) :=
      (IsPullback.of_hasPullback (limit.π D (op i)) (𝟙 (D.obj (op i)))).isIso_fst_of_isIso
    have key : M.mapLimit = pullback.fst (limit.π D (op i)) Yi.hom ≫
          inv (pullback.fst (limit.π D (op i)) (𝟙 (D.obj (op i)))) :=
      (IsIso.eq_comp_inv (pullback.fst (limit.π D (op i)) (𝟙 (D.obj (op i))))).2
        M.mapLimit_fst
    rw [key]
    exact isEtale_comp B _ hZ hfstLim (isEtale_of_iso B _ hZ
      (asIso (pullback.fst (limit.π D (op i)) (𝟙 (D.obj (op i))))).symm)
  obtain ⟨j, hij, hj⟩ := M.exists_isEtale_mapAt hmapLim hYifp.1
  -- Stacks 07SR: the base changes to the stages are schemes from some stage `k₁` on
  let DS := MorphismDescentSystem.stagesSourceDescentSituation M
  have hDSrep : DS.limitCone.pt.IsRepresentable :=
    isRepresentable_of_natIso (yoneda.obj W) e0
  obtain ⟨k₁, hk₁⟩ := DS.exists_isRepresentable_system_obj_of_mk_lt
    (MorphismDescentSystem.mk_stages_lt M) hDSrep
  obtain ⟨i₀, hji₀, hk₁i₀⟩ := exists_ge_ge j k₁.1
  have hi₀ : i ≤ i₀ := hij.trans hji₀
  let k₀ : MorphismDescentSystem.Stages M := ⟨i₀, hi₀⟩
  have hk : k₁ ≤ k₀ := hk₁i₀
  -- the base change to the stage `i₀` is a scheme, being affine over the one at `k₁`
  have hrel := (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B _ hZ
    (DS.algebraicSpace k₀) (DS.algebraicSpace k₁) (DS.transition_affine (homOfLE hk).op)).1
  have _ := hk₁
  let T₁ := hrel.pullback (DS.system.obj (op k₁)).reprW.hom
  have hI₁ : IsIso (hrel.fst (DS.system.obj (op k₁)).reprW.hom) :=
    (hrel.isPullback (DS.system.obj (op k₁)).reprW.hom).isIso_fst_of_isIso
  let eT : yoneda.obj T₁ ≅ pullback (D.map (homOfLE hi₀).op) Yi.hom :=
    @asIso _ _ _ _ (hrel.fst (DS.system.obj (op k₁)).reprW.hom) hI₁
  have hP₀alg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ
      (pullback (D.map (homOfLE hi₀).op) Yi.hom) := DS.algebraicSpace k₀
  have hPjalg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ
      (pullback (D.map (homOfLE hij).op) Yi.hom) := DS.algebraicSpace ⟨j, hij⟩
  -- it is étale over `D i₀`, as a base change of the étale base change to `j`
  have hfstj : IsEtale B (⊤_ Scheme.{u}) hZ (pullback.fst (D.map (homOfLE hij).op) Yi.hom) := by
    have _ : IsIso (pullback.fst (D.map (homOfLE hij).op) (𝟙 (D.obj (op i)))) :=
      (IsPullback.of_hasPullback (D.map (homOfLE hij).op) (𝟙 (D.obj (op i)))).isIso_fst_of_isIso
    have key : pullback.fst (D.map (homOfLE hij).op) Yi.hom =
        M.mapAt j hij ≫ pullback.fst (D.map (homOfLE hij).op) (𝟙 (D.obj (op i))) :=
      (M.mapAt_fst j hij).symm
    rw [key]
    exact isEtale_comp B _ hZ hj (isEtale_of_iso B _ hZ
      (asIso (pullback.fst (D.map (homOfLE hij).op) (𝟙 (D.obj (op i))))))
  have hsq := isPullback_baseChangeOverMap B _ hZ (D.map (homOfLE hi₀).op)
    (D.map (homOfLE hij).op) (D.map (homOfLE hji₀).op)
    ((D.map_comp _ _).symm.trans (congrArg D.map (Subsingleton.elim _ _))) Yi.hom
  have hfst₀ : IsEtale B (⊤_ Scheme.{u}) hZ (pullback.fst (D.map (homOfLE hi₀).op) Yi.hom) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B hP₀alg hPjalg (hD _) (hD _) hsq hfstj
  let t : yoneda.obj T₁ ⟶ D.obj (op i₀) := eT.hom ≫ pullback.fst (D.map (homOfLE hi₀).op) Yi.hom
  have ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      T).presheaf t := (isEtale_iff_presheaf_of_yoneda B _ hZ t).1
    (isEtale_comp B _ hZ (isEtale_of_iso B _ hZ eT) hfst₀)
  -- its underlying scheme is quasi-compact and quasi-separated
  have _ : CompactSpace (T.obj T₁) := compactSpace_of_isQuasiCompactSpace_yoneda_obj B _ hZ
    (isQuasiCompactSpace_of_iso B _ hZ eT.symm (DS.quasiCompact k₀))
  have _ : QuasiSeparatedSpace (T.obj T₁) := by
    have hT₁qs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (yoneda.obj T₁) :=
      isQuasiSeparatedOver_of_iso B _ hZ
        ((OverShriek.relocalizePresheafFunctor _).mapIso eT.symm) (DS.quasiSeparated k₀)
    -- the structure morphism to the terminal object of the site is quasi-separated
    let Tz : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))
    let m : T₁ ⟶ Tz := Over.homMk T₁.hom (Category.comp_id _)
    have _ : QuasiSeparated (T.map m) := (isQuasiSeparated_yoneda_map_iff B _ hZ m).1
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B _ hZ hZ
        (isAlgebraicSpace_yoneda B _ hZ T₁) hT₁qs _)
    have _ : QuasiSeparatedSpace (T.obj Tz) :=
      (inferInstance : QuasiSeparatedSpace (⊤_ Scheme.{u}))
    exact quasiSeparatedSpace_of_quasiSeparated (T.map m)
  -- `W` is its base change to the limit
  let leg : pullback (limit.π D (op i)) Yi.hom ⟶ pullback (D.map (homOfLE hi₀).op) Yi.hom :=
    baseChangeOverMap B _ hZ (limit.π D (op i)) (D.map (homOfLE hi₀).op) (limit.π D (op i₀))
      (limit.w D (homOfLE hi₀).op) Yi.hom
  have hleg := isPullback_baseChangeOverMap B _ hZ (limit.π D (op i))
    (D.map (homOfLE hi₀).op) (limit.π D (op i₀)) (limit.w D (homOfLE hi₀).op) Yi.hom
  let a : W ⟶ T₁ := yoneda.preimage (e0.hom ≫ leg ≫ eT.inv)
  have ha : IsPullback (yoneda.map a) w t (π.app (op i₀)) := by
    refine hleg.of_iso e0.symm eT.symm eU.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [a, leg]
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, he0, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp [t]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← heU, Iso.inv_hom_id_assoc]
  exact ⟨i₀, exists_etale_scheme_models_of_stage B hZ hI D hD hA π hπ w i₀ T₁ t ht a ha⟩

end Space

end AlgebraicGeometry

end
