module

public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeTorsorSectionsGenericPoint
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Facts
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Torsors under an abelian scheme with a section over the generic point

Let `W` be a regular integral Noetherian scheme of dimension at most `n` with function field `K`
and let `G → W` be an abelian scheme. This file reduces the statement that an fppf `G`-torsor with
a section over `Spec K` is trivial — the hypothesis `htrivial` of
`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective` (Stacks 0AF9 for `n = 2`, and
Stacks 0H8E for every `n`) — to two inputs, taken here as explicit hypotheses:

* `hext`: over an integral Noetherian regular scheme `X` of dimension at most `n`, a section of a
  proper group scheme `H → X` over the generic point of `X` extends to a section over `X`;
* `hloc`: every fppf torsor under a smooth commutative group scheme over `W` has, around every
  point of `W`, a section over an affine scheme étale over `W`.

## Main results

* `AlgebraicGeometry.smooth_of_isAbelianScheme`: an abelian scheme is smooth.
* `AlgebraicGeometry.isTrivial_of_nonempty_genericPoint_of_extend_of_local`: given `hext` and
  `hloc`, an fppf `G`-torsor with a section over `Spec K` is trivial.

## Implementation notes

The proof is the gluing argument. Let `s` be the section over `Spec K`. Around each point `w`
of `W` there is, by `hloc`, an affine scheme `U` étale over `W` with a section `t` of the torsor
`P`; `U` is regular, hence normal and Noetherian, hence a finite disjoint union of integral
schemes, and we replace `U` by the component `V` through a point over `w`. Then `V` is integral,
Noetherian, regular and of dimension at most `n`, the last because an étale morphism is locally
quasi-finite and so does not raise the dimension. Over `V_K = V ×_W Spec K` the sections `s`
and `t` differ by a point `δ` of `G`; restricted to the generic point of `V` it is a rational
section of `G ×_W V → V`, which `hext` extends to a section `g` over `V`. Since `V_K` is reduced
and the generic point of `V` is dense in it (`V_K → V` is a preimmersion), `g` restricts to `δ`
on `V_K`, so `g · t` restricts to `s` on `V_K`. Two such sections over `V` and `V'` agree on
`V ×_W V'`: that scheme is reduced, being étale over `V`, and its base change to `Spec K` is
dense in it, because `V ×_W V' → W` is flat and hence generalizing; a section of `G` which
vanishes on a dense subscheme of a reduced scheme vanishes, `G` being separated. The family of
the `V` is an fppf covering of `W`, so the sections glue to a global section, and a torsor with a
global section is trivial.

All schemes are built as concrete fibre products of schemes and placed in the big fppf site
through its closure under fibre products and open subschemes; nothing about the site's own
choice of limits is used.

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.MonObj

universe u

/-! ### Torsors -/

section Torsor

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- If a restriction map of a sheaf of groups is injective, so is the corresponding restriction
map of every pseudo-torsor under it: two sections over the source differ by a group element, which
restricts to the identity, hence is the identity. -/
public theorem PseudoTorsor.injective_presheaf_map_of_injective {𝒢 : SheafOfGroups J}
    (P : PseudoTorsor 𝒢) {U V : Cᵒᵖ} (f : U ⟶ V)
    (h : Function.Injective (𝒢.presheaf.map f)) : Function.Injective (P.presheaf.map f) := by
  intro a b hab
  obtain ⟨g, hg, -⟩ := P.simplyTransitive U ⟨a⟩ a b
  have h1 : P.act V (𝒢.presheaf.map f g) (P.presheaf.map f a) = P.presheaf.map f a := by
    rw [← P.naturality, hg, hab]
  obtain ⟨g₀, -, huniq⟩ :=
    P.simplyTransitive V ⟨P.presheaf.map f a⟩ (P.presheaf.map f a) (P.presheaf.map f a)
  have h2 : 𝒢.presheaf.map f g = 1 := (huniq _ h1).trans (huniq _ (P.one_act _ _)).symm
  have h3 : g = 1 := h (h2.trans (SheafOfGroups.map_one f).symm)
  rw [← hg, h3, P.one_act]

end Torsor

namespace AlgebraicGeometry

/-! ### Scheme-theoretic facts -/

/-- **An abelian scheme is smooth**: it is flat and locally of finite presentation, and its
fibres are abelian varieties, which are smooth. -/
public theorem smooth_of_isAbelianScheme {W : Scheme.{u}} (G : Over W) [GrpObj G]
    [IsAbelianScheme G] : Smooth G.hom := by
  refine Smooth.of_smooth_fiberToSpecResidueField G.hom fun x => ?_
  let M := (Over.pullback (W.fromSpecResidueField x)).mapGrp.obj (.mk G)
  have h := IsAbelianScheme.fibre_isAbelianVariety (G := G) x
  exact @smooth_of_isAbelianVariety (W.residueField x) _ M.X M.grp h

/-- A flat morphism of irreducible schemes sends the generic point to the generic point: it is
generalizing, and the generic point has no proper generalization. -/
public theorem map_genericPoint_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IrreducibleSpace X] [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨x', hx', he⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  rw [← he, Inseparable.eq (Specializes.antisymm (genericPoint_specializes x') hx')]

/-- A morphism sending `x` to `y` induces a morphism of the spectra of the local rings compatible
with the canonical morphisms to the two schemes. -/
public theorem exists_comp_fromSpecStalk_eq_fromSpecStalk_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {x : X} {y : Y} (h : f x = y) : ∃ a : Spec (X.presheaf.stalk x) ⟶ Spec (Y.presheaf.stalk y),
      a ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
  subst h
  exact ⟨_, Scheme.SpecMap_stalkMap_fromSpecStalk f⟩

/-- The base change of a flat morphism to the generic point of an irreducible target is
dominant: every point of the source generalizes to a point over the generic point. -/
public theorem isDominant_pullback_fst_fromSpecStalk_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IrreducibleSpace Y] :
    IsDominant (pullback.fst f (Y.fromSpecStalk (genericPoint Y))) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨x', hx', he⟩ := Flat.generalizingMap f (genericPoint_specializes (f x))
  have hmem : x' ∈ Set.range (pullback.fst f (Y.fromSpecStalk (genericPoint Y))) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, he, Scheme.range_fromSpecStalk]
    exact specializes_rfl
  exact hx'.mem_closed isClosed_closure (subset_closure hmem)

/-- A morphism whose composite with a preimmersion is dominant is dominant: a preimmersion is a
topological embedding, and closures in its source are preimages of closures in its target. -/
public theorem isDominant_of_isDominant_comp_of_isPreimmersion {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (p : Y ⟶ Z) [IsPreimmersion p] [IsDominant (j ≫ p)] : IsDominant j := by
  refine ⟨fun y => ?_⟩
  rw [(IsPreimmersion.isEmbedding p).isInducing.closure_eq_preimage_closure_image,
    Set.mem_preimage, ← Set.range_comp]
  have h := (inferInstance : IsDominant (j ≫ p)).denseRange (p y)
  simpa only [Scheme.Hom.comp_base, TopCat.coe_comp] using h

/-! ### Objects of the big fppf site over `W` -/

variable {B : BigFppfSite.{u}} {W : Scheme.{u}} {hW : B.Contains W}

/-- The base change `X ×_W Spec K` of an object of the big fppf site over an irreducible `W` to
the generic point of `W`, as an object of the site. -/
public def genericFibre [IrreducibleSpace W] (hK : B.Contains (Spec W.functionField))
    (X : BigFppfOver B W hW) : BigFppfOver B W hW :=
  siteObject B W hW
    (Scheme.size_pullback_lt X.hom.hom (W.fromSpecStalk (genericPoint W)) X.left.property hK)
    (pullback.snd X.hom.hom (W.fromSpecStalk (genericPoint W)) ≫
      W.fromSpecStalk (genericPoint W))

/-- The projection `X ×_W Spec K ⟶ X`. -/
public def genericFibreFst [IrreducibleSpace W] (hK : B.Contains (Spec W.functionField))
    (X : BigFppfOver B W hW) : genericFibre hK X ⟶ X :=
  Over.homMk (ObjectProperty.homMk
    (pullback.fst X.hom.hom (W.fromSpecStalk (genericPoint W)))) (by
    apply ObjectProperty.hom_ext
    exact pullback.condition)

/-- The projection `X ×_W Spec K ⟶ Spec K`. -/
public def genericFibreSnd [IrreducibleSpace W] (hK : B.Contains (Spec W.functionField))
    (X : BigFppfOver B W hW) : genericFibre hK X ⟶ genericPointObj B W hW hK :=
  Over.homMk (ObjectProperty.homMk
    (pullback.snd X.hom.hom (W.fromSpecStalk (genericPoint W)))) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The base change to the generic point of a morphism of the big fppf site over `W`. -/
public def genericFibreMap [IrreducibleSpace W] (hK : B.Contains (Spec W.functionField))
    {X Y : BigFppfOver B W hW} (f : X ⟶ Y) : genericFibre hK X ⟶ genericFibre hK Y :=
  Over.homMk (ObjectProperty.homMk (pullback.lift (pullback.fst _ _ ≫ f.left.hom)
    (pullback.snd _ _) (by
      have hf : f.left.hom ≫ Y.hom.hom = X.hom.hom := congrArg (fun g => g.hom) (Over.w f)
      have h : (pullback.fst X.hom.hom (W.fromSpecStalk (genericPoint W)) ≫ f.left.hom) ≫
          Y.hom.hom = pullback.snd X.hom.hom (W.fromSpecStalk (genericPoint W)) ≫
            W.fromSpecStalk (genericPoint W) := by
        rw [Category.assoc, hf]
        exact pullback.condition
      exact h))) (by
    apply ObjectProperty.hom_ext
    exact pullback.lift_snd_assoc _ _ _ _)

/-- The base change of `f` to the generic point commutes with the projections to `X` and `Y`. -/
@[reassoc]
public theorem genericFibreMap_fst [IrreducibleSpace W] (hK : B.Contains (Spec W.functionField))
    {X Y : BigFppfOver B W hW} (f : X ⟶ Y) :
    genericFibreMap hK f ≫ genericFibreFst hK Y = genericFibreFst hK X ≫ f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact pullback.lift_fst _ _ _

/-- The base change of `f` to the generic point commutes with the projections to `Spec K`. -/
public theorem genericFibreMap_snd [IrreducibleSpace W] (hK : B.Contains (Spec W.functionField))
    {X Y : BigFppfOver B W hW} (f : X ⟶ Y) :
    genericFibreMap hK f ≫ genericFibreSnd hK Y = genericFibreSnd hK X := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact pullback.lift_snd _ _ _

/-- The fibre product `X ×_W Y` of two objects of the big fppf site over `W`. -/
public def fibreProductObj (X Y : BigFppfOver B W hW) : BigFppfOver B W hW :=
  siteObject B W hW (Scheme.size_pullback_lt X.hom.hom Y.hom.hom X.left.property Y.left.property)
    (pullback.fst X.hom.hom Y.hom.hom ≫ X.hom.hom)

/-- The first projection `X ×_W Y ⟶ X`. -/
public def fibreProductFst (X Y : BigFppfOver B W hW) : fibreProductObj X Y ⟶ X :=
  Over.homMk (ObjectProperty.homMk (pullback.fst X.hom.hom Y.hom.hom)) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The second projection `X ×_W Y ⟶ Y`. -/
public def fibreProductSnd (X Y : BigFppfOver B W hW) : fibreProductObj X Y ⟶ Y :=
  Over.homMk (ObjectProperty.homMk (pullback.snd X.hom.hom Y.hom.hom)) (by
    apply ObjectProperty.hom_ext
    exact pullback.condition.symm)

/-- The morphism into `X ×_W Y` given by morphisms into the two factors. -/
public def fibreProductLift {X Y Z : BigFppfOver B W hW} (a : Z ⟶ X) (b : Z ⟶ Y) :
    Z ⟶ fibreProductObj X Y :=
  Over.homMk (ObjectProperty.homMk (pullback.lift a.left.hom b.left.hom (by
      have ha : a.left.hom ≫ X.hom.hom = Z.hom.hom := congrArg (fun g => g.hom) (Over.w a)
      have hb : b.left.hom ≫ Y.hom.hom = Z.hom.hom := congrArg (fun g => g.hom) (Over.w b)
      rw [ha, hb]))) (by
    apply ObjectProperty.hom_ext
    have ha : a.left.hom ≫ X.hom.hom = Z.hom.hom := congrArg (fun g => g.hom) (Over.w a)
    change pullback.lift a.left.hom b.left.hom _ ≫ pullback.fst X.hom.hom Y.hom.hom ≫ X.hom.hom =
      Z.hom.hom
    rw [pullback.lift_fst_assoc, ha])

/-- The first component of `fibreProductLift a b` is `a`. -/
public theorem fibreProductLift_fst {X Y Z : BigFppfOver B W hW} (a : Z ⟶ X) (b : Z ⟶ Y) :
    fibreProductLift a b ≫ fibreProductFst X Y = a := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact pullback.lift_fst _ _ _

/-- The second component of `fibreProductLift a b` is `b`. -/
public theorem fibreProductLift_snd {X Y Z : BigFppfOver B W hW} (a : Z ⟶ X) (b : Z ⟶ Y) :
    fibreProductLift a b ≫ fibreProductSnd X Y = b := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact pullback.lift_snd _ _ _

/-! ### Points of `G` -/

/-- **Restriction of points of a separated group scheme along a dominant morphism to a reduced
object is injective.** -/
public theorem injective_pointsSheaf_map_of_isDominant (G : Over W) [GrpObj G] [IsCommMonObj G]
    [IsSeparated G.hom] (hG : B.Contains G.left) {X Y : BigFppfOver B W hW} (f : X ⟶ Y)
    [IsReduced Y.left.obj] [IsDominant f.left.hom] :
    Function.Injective
      ((Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (pointsSheaf B W hW G hG)).presheaf.map
        f.op) := by
  intro a b hab
  let a' : (Over.post (X := B.obj hW) B.inclusion).obj Y ⟶ G := a
  let b' : (Over.post (X := B.obj hW) B.inclusion).obj Y ⟶ G := b
  have key : (Over.post (X := B.obj hW) B.inclusion).map f ≫ a' =
      (Over.post (X := B.obj hW) B.inclusion).map f ≫ b' := hab
  have hleft := congrArg Over.Hom.left key
  rw [Over.comp_left, Over.comp_left] at hleft
  have : IsReduced (unop ((Over.post (X := B.obj hW) B.inclusion).op.obj (op Y))).left :=
    inferInstanceAs (IsReduced Y.left.obj)
  have : IsDominant ((Over.post (X := B.obj hW) B.inclusion).map f).left :=
    inferInstanceAs (IsDominant f.left.hom)
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom
    ((Over.w a').trans (Over.w b').symm) _ hleft)

/-- **A point of `G` over `V ×_W Spec K` extends to `V`**, for `V` integral, Noetherian, regular,
of dimension at most `n` and étale over `W`, granted the extension property `hext` of rational
sections of proper group schemes over such bases. -/
public theorem exists_comp_genericFibreFst_eq [IsIntegral W]
    (hK : B.Contains (Spec W.functionField)) {n : WithBot ℕ∞}
    (hext : ∀ (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X], IsRegular X →
      topologicalKrullDim X ≤ n →
      ∀ (H : Over X) [GrpObj H] [IsProper H.hom] (σ : Spec X.functionField ⟶ H.left),
        σ ≫ H.hom = X.fromSpecStalk (genericPoint X) →
        ∃ g : X ⟶ H.left, g ≫ H.hom = 𝟙 X ∧ X.fromSpecStalk (genericPoint X) ≫ g = σ)
    (G : Over W) [GrpObj G] [IsProper G.hom]
    (V : BigFppfOver B W hW) [IsIntegral V.left.obj] [IsNoetherian V.left.obj]
    (hVreg : IsRegular V.left.obj) (hVdim : topologicalKrullDim V.left.obj ≤ n)
    [Etale V.hom.hom]
    (δ : (Over.post (X := B.obj hW) B.inclusion).obj (genericFibre hK V) ⟶ G) :
    ∃ g : (Over.post (X := B.obj hW) B.inclusion).obj V ⟶ G,
      (Over.post (X := B.obj hW) B.inclusion).map (genericFibreFst hK V) ≫ g = δ := by
  let f : V.left.obj ⟶ W := V.hom.hom
  have hgen : f (genericPoint V.left.obj) = genericPoint W := map_genericPoint_eq_of_flat f
  obtain ⟨a, ha⟩ := exists_comp_fromSpecStalk_eq_fromSpecStalk_comp f hgen
  let j : Spec V.left.obj.functionField ⟶ pullback f (W.fromSpecStalk (genericPoint W)) :=
    pullback.lift (V.left.obj.fromSpecStalk (genericPoint V.left.obj)) a ha.symm
  have hjfst : j ≫ pullback.fst _ _ = V.left.obj.fromSpecStalk (genericPoint V.left.obj) :=
    pullback.lift_fst _ _ _
  have : IsDominant (j ≫ pullback.fst f (W.fromSpecStalk (genericPoint W))) := by
    rw [hjfst]; exact isDominant_fromSpecStalk_genericPoint _
  have hjdom : IsDominant j := isDominant_of_isDominant_comp_of_isPreimmersion j (pullback.fst _ _)
  have hred : IsReduced (pullback f (W.fromSpecStalk (genericPoint W))) :=
    isReduced_of_etale (pullback.snd f (W.fromSpecStalk (genericPoint W)))
  let M := (Over.pullback f).mapGrp.obj (.mk G)
  have : IsProper M.X.hom := inferInstanceAs (IsProper (pullback.snd G.hom f))
  let δl : pullback f (W.fromSpecStalk (genericPoint W)) ⟶ G.left := δ.left
  have hδ : δl ≫ G.hom = pullback.snd f (W.fromSpecStalk (genericPoint W)) ≫
      W.fromSpecStalk (genericPoint W) := Over.w δ
  let fstG : M.X.left ⟶ G.left := pullback.fst G.hom f
  let sndG : M.X.left ⟶ V.left.obj := pullback.snd G.hom f
  have hcond : fstG ≫ G.hom = sndG ≫ f := pullback.condition
  have hσc : (j ≫ δl) ≫ G.hom = V.left.obj.fromSpecStalk (genericPoint V.left.obj) ≫ f := by
    rw [Category.assoc, hδ, ← Category.assoc, pullback.lift_snd, ha]
  let σ : Spec V.left.obj.functionField ⟶ M.X.left :=
    pullback.lift (j ≫ δl) (V.left.obj.fromSpecStalk (genericPoint V.left.obj)) hσc
  have hσ₁ : σ ≫ fstG = j ≫ δl := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ M.X.hom = V.left.obj.fromSpecStalk (genericPoint V.left.obj) :=
    pullback.lift_snd _ _ _
  obtain ⟨g₀, hg₀, hg₀'⟩ := hext V.left.obj hVreg hVdim M.X σ hσ₂
  have hg₀s : g₀ ≫ sndG = 𝟙 _ := hg₀
  have hgw : (g₀ ≫ fstG) ≫ G.hom = f := by
    rw [Category.assoc, hcond, ← Category.assoc, hg₀s, Category.id_comp]
  refine ⟨Over.homMk (g₀ ≫ fstG) hgw, ?_⟩
  apply Over.OverMorphism.ext
  change pullback.fst f (W.fromSpecStalk (genericPoint W)) ≫ g₀ ≫ fstG = δl
  refine ext_of_isDominant_of_isSeparated (X := pullback f (W.fromSpecStalk (genericPoint W)))
    G.hom ?_ j ?_
  · rw [hδ, Category.assoc, hgw]
    exact pullback.condition
  · rw [← Category.assoc j, hjfst, ← Category.assoc, hg₀', hσ₁]

/-- **An affine scheme étale over a regular scheme is covered by integral Noetherian open
subschemes**: being regular it is normal and Noetherian, hence a finite disjoint union of normal
integral schemes (Stacks 033M), and the component through the given point is open. -/
public theorem exists_isIntegral_isNoetherian_of_etale (hreg : IsRegular W)
    (U : BigFppfOver B W hW) (hUet : Etale U.hom.hom) (hUaff : IsAffine U.left.obj)
    (u : U.left.obj) :
    ∃ (V : BigFppfOver B W hW) (_ : V ⟶ U) (v : V.left.obj), IsIntegral V.left.obj ∧
      IsNoetherian V.left.obj ∧ Etale V.hom.hom ∧ V.hom.hom v = U.hom.hom u := by
  have hUreg : IsRegular U.left.obj := isRegular_of_etale U.hom.hom hreg
  have : IsLocallyNoetherian U.left.obj := isLocallyNoetherian_of_isRegular hUreg
  have : IsNoetherian U.left.obj := {}
  obtain ⟨I, _, Y, -, hYi, ⟨eU⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal U.left.obj).mp
      (isNormal_of_isRegular _ hUreg)
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover Y).exists_eq (eU.hom u)
  let k : Y i ⟶ U.left.obj := Sigma.ι Y i ≫ eU.inv
  have hk : IsOpenImmersion k := inferInstance
  have hYc : B.Contains (Y i) := B.contains_of_isOpenImmersion k U.left.property
  have hku : k y = u := by
    change eU.inv (Sigma.ι Y i y) = u
    have hy' : Sigma.ι Y i y = eU.hom u := hy
    rw [hy', ← Scheme.Hom.comp_apply, eU.hom_inv_id]
    rfl
  have : Etale (k ≫ U.hom.hom) := inferInstance
  have : IsLocallyNoetherian (Y i) :=
    isLocallyNoetherian_of_isRegular (isRegular_of_etale (k ≫ U.hom.hom) hreg)
  have : CompactSpace (Y i) := by
    have hc : IsCompact (⇑k '' Set.univ) := TopologicalSpace.NoetherianSpace.isCompact _
    exact isCompact_univ_iff.mp ((Scheme.Hom.isOpenEmbedding k).isInducing.isCompact_iff.mpr hc)
  have hYn : IsNoetherian (Y i) := {}
  refine ⟨siteObject B W hW hYc (k ≫ U.hom.hom),
    Over.homMk (ObjectProperty.homMk k) (by apply ObjectProperty.hom_ext; rfl), y, hYi i, hYn,
    inferInstanceAs (Etale (k ≫ U.hom.hom)), ?_⟩
  change U.hom.hom (k y) = _
  rw [hku]

/-! ### The gluing -/

/-- **An fppf torsor under an abelian scheme with a section over the generic point is
trivial**, for `W` a regular integral Noetherian scheme of dimension at most `n` with function
field `K`, granted the two inputs `hext` and `hloc`:

* `hext`: over an integral Noetherian regular scheme `X` of dimension at most `n`, every section
  over the generic point of a proper group scheme over `X` extends to a section over `X`;
* `hloc`: every fppf torsor under a smooth commutative group scheme over `W` has, around every
  point of `W`, a section over an affine scheme étale over `W`.

The conclusion is the hypothesis `htrivial` of
`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective`. See the module docstring for the
gluing argument. -/
public theorem isTrivial_of_nonempty_genericPoint_of_extend_of_local
    (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    {n : WithBot ℕ∞} (hdim : topologicalKrullDim (W : Type u) ≤ n)
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    (hext : ∀ (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X], IsRegular X →
      topologicalKrullDim X ≤ n →
      ∀ (H : Over X) [GrpObj H] [IsProper H.hom] (σ : Spec X.functionField ⟶ H.left),
        σ ≫ H.hom = X.fromSpecStalk (genericPoint X) →
        ∃ g : X ⟶ H.left, g ≫ H.hom = 𝟙 X ∧ X.fromSpecStalk (genericPoint X) ≫ g = σ)
    (hloc : ∀ (G' : Over W) [GrpObj G'] [IsCommMonObj G'] [Smooth G'.hom]
      (hG' : B.Contains G'.left)
      (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G' hG')) (w : W),
      ∃ (U : BigFppfOver B W hW) (u : U.left.obj), Etale (B.inclusion.map U.hom) ∧
        IsAffine U.left.obj ∧ (B.inclusion.map U.hom).base u = w ∧
        Nonempty (F.1.presheaf.obj (op U))) :
    ∀ F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG),
      Nonempty (F.1.presheaf.obj (op (genericPointObj B W hW hK))) → F.1.IsTrivial := by
  intro F ⟨s⟩
  have : Smooth G.hom := smooth_of_isAbelianScheme G
  let P := F.1
  have hmap : ∀ {X Y Z : BigFppfOver B W hW} (a : X ⟶ Y) (b : Y ⟶ Z) (z : P.presheaf.obj (op Z)),
      P.presheaf.map (a ≫ b).op z = P.presheaf.map a.op (P.presheaf.map b.op z) := by
    intro X Y Z a b z
    rw [op_comp, Functor.map_comp_apply]
  choose U u hUet hUaff hUu hUt using hloc G hG F
  choose V e v hVi hVn hVet hVv using fun w =>
    exists_isIntegral_isNoetherian_of_etale hreg (U w) (hUet w) (hUaff w) (u w)
  have hx : ∀ w, ∃ x : P.presheaf.obj (op (V w)),
      P.presheaf.map (genericFibreFst hK (V w)).op x =
        P.presheaf.map (genericFibreSnd hK (V w)).op s := by
    intro w
    have := hVi w
    have := hVn w
    have := hVet w
    let t : P.presheaf.obj (op (V w)) := P.presheaf.map (e w).op (hUt w).some
    obtain ⟨δ, hδ, -⟩ := P.simplyTransitive _ ⟨P.presheaf.map (genericFibreFst hK (V w)).op t⟩
      (P.presheaf.map (genericFibreFst hK (V w)).op t)
      (P.presheaf.map (genericFibreSnd hK (V w)).op s)
    obtain ⟨g, hg⟩ := exists_comp_genericFibreFst_eq hK hext G (V w)
      (isRegular_of_etale (V w).hom.hom hreg)
      ((topologicalKrullDim_le_of_etale (V w).hom.hom).trans hdim) δ
    let g' : (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf
      (pointsSheaf B W hW G hG)).presheaf.obj (op (V w)) := g
    have hg' : (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf
      (pointsSheaf B W hW G hG)).presheaf.map (genericFibreFst hK (V w)).op g' = δ := hg
    refine ⟨P.act _ g' t, ?_⟩
    rw [P.naturality, hg']
    exact hδ
  choose x hx using hx
  let π : ∀ w : W, V w ⟶ Over.mk (𝟙 (B.obj hW)) := fun w => Over.homMk (V w).hom (by simp)
  have hmem : Sieve.ofArrows V π ∈ BigFppfOver.topology B W hW (Over.mk (𝟙 (B.obj hW))) := by
    refine FormalSpace.fppf_ofArrows_mem B W hW V π (fun w => ?_) (fun w => ?_)
      (fun w => ⟨w, v w, ?_⟩)
    · have := hVet w
      exact inferInstanceAs (Flat (V w).hom.hom)
    · have := hVet w
      exact inferInstanceAs (LocallyOfFinitePresentation (V w).hom.hom)
    · change (V w).hom.hom (v w) = w
      rw [hVv w]
      exact hUu w
  have hP : Presieve.IsSheaf (BigFppfOver.topology B W hW) P.presheaf :=
    (isSheaf_iff_isSheaf_of_type _ _).mp P.isSheaf
  have hsf := (Presieve.isSheafFor_iff_generate (P := P.presheaf)
    (Presieve.ofArrows V π)).2 (hP _ hmem)
  rw [Presieve.isSheafFor_arrows_iff] at hsf
  obtain ⟨t, -, -⟩ := hsf x (by
    intro w₁ w₂ Z g₁ g₂ _
    have := hVi w₁
    have := hVet w₁
    have := hVet w₂
    let Q := fibreProductObj (V w₁) (V w₂)
    have := hVi w₂
    have hQred' : IsReduced (pullback (V w₁).hom.hom (V w₂).hom.hom) :=
      isReduced_of_etale (pullback.snd (V w₁).hom.hom (V w₂).hom.hom)
    have hQred : IsReduced Q.left.obj := hQred'
    have : Etale Q.hom.hom := by
      have h : Etale (pullback.snd (V w₁).hom.hom (V w₂).hom.hom ≫ (V w₂).hom.hom) :=
        inferInstance
      rw [← pullback.condition] at h
      exact h
    have : IsDominant (genericFibreFst hK Q).left.hom :=
      isDominant_pullback_fst_fromSpecStalk_genericPoint (Y := W) (X := Q.left.obj) Q.hom.hom
    have hQ : P.presheaf.map (fibreProductFst (V w₁) (V w₂)).op (x w₁) =
        P.presheaf.map (fibreProductSnd (V w₁) (V w₂)).op (x w₂) := by
      apply P.injective_presheaf_map_of_injective (genericFibreFst hK Q).op
        (injective_pointsSheaf_map_of_isDominant G hG (genericFibreFst hK Q))
      rw [← hmap, ← hmap, ← genericFibreMap_fst, ← genericFibreMap_fst, hmap, hmap, hx, hx,
        ← hmap, ← hmap, genericFibreMap_snd, genericFibreMap_snd]
    have h₁ : P.presheaf.map g₁.op (x w₁) = P.presheaf.map (fibreProductLift g₁ g₂).op
        (P.presheaf.map (fibreProductFst (V w₁) (V w₂)).op (x w₁)) := by
      rw [← hmap, fibreProductLift_fst]
    have h₂ : P.presheaf.map g₂.op (x w₂) = P.presheaf.map (fibreProductLift g₁ g₂).op
        (P.presheaf.map (fibreProductSnd (V w₁) (V w₂)).op (x w₂)) := by
      rw [← hmap, fibreProductLift_snd]
    rw [h₁, h₂, hQ])
  exact PseudoTorsor.isTrivial_of_terminal_section Over.mkIdTerminal F.1 t

end AlgebraicGeometry

end
