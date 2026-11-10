module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.TopologicalInvariance.SpacesEtaleFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalHomeomorphismRepresentable

/-!
# Topological invariance of the spaces-étale site (Stacks 05ZH)

Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of algebraic
spaces over a scheme `S`. Base change `V ↦ X ×_Y V` is an equivalence from the spaces-étale site
of `Y` to that of `X`. This is Stacks 05ZH, with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Space.exists_chart_universalHomeomorphism_of_isIntegralHom`: over an étale
  chart `Z` of `Y` the morphism `f` restricts to a universal homeomorphism of schemes
  `X ×_Y Z ⟶ Z`.
* `AlgebraicGeometry.Space.exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism`:
  Stacks 04DZ on the big fppf site, in the cartesian form a lifted étale presentation asks for.
* `AlgebraicGeometry.Space.nonempty_liftedEtalePresentation_of_isIntegralHom`: every object of
  the spaces-étale site of `X` admits a lifted étale presentation across `f`.
* `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isIntegralHom`: base change along `f` is
  essentially surjective.
* `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isIntegralHom`: **Stacks 05ZH.**

## Implementation notes

The argument is the source's. Faithfulness is
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective` and fullness is
`AlgebraicGeometry.Space.full_spacesBaseChange_of_universalHomeomorphism`, `f` being a universal
homeomorphism by `AlgebraicGeometry.Space.universalHomeomorphism_of_isIntegralHom`.

For essential surjectivity, an object `C` of the spaces-étale site of `X` is presented by a
surjective étale chart `U ⟶ C` and its kernel pair `R`, chosen over the base change `J = X ×_Y Z`
of an étale chart `Z ⟶ Y`. The morphism `J ⟶ Z` is a universal homeomorphism of schemes (Stacks
05Z4), so `U` and `R`, étale over `J`, lift to schemes `V` and `W` étale over `Z` by Stacks 04DZ,
`Stacks.Etale.exists_etale_pullback_iso`; the lifts lie in the site because they are étale over
`Z` and homeomorphic to `U` and `R`. The two projections `R ⇉ U` descend to `W ⇉ V` by fullness,
and the result is an étale equivalence relation by faithfulness — this is the source's
"by fully faithfulness of the functor we obtain morphisms `s, t : V'' ⟶ V'`". Its quotient is the
required object of the spaces-étale site of `Y`, by
`AlgebraicGeometry.Space.mem_essImage_spacesBaseChange_of_liftedEtalePresentation`.

Joint monicity of `W ⇉ V` is the one place where the thickening argument of
`AlgebraicGeometry.Space.nonempty_liftedEtalePresentation_of_isThickening` used that its `f` is a
monomorphism; here two morphisms into `U = V ×_Y X` are compared through both of their components
instead.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 05Z4](https://stacks.math.columbia.edu/tag/05Z4)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart-level universal homeomorphism -/

section Chart

variable {X Y : AlgebraicSpaces B S hS}

/-- **An integral universal homeomorphism restricts to a universal homeomorphism of schemes over
every chart of its target.** For `ζ : Z ⟶ Y` with `Z` an object of the site, the base change of
`f` along `ζ` is represented by an object `J` of the site, and the morphism `J ⟶ Z` is a
universal homeomorphism of schemes, by Stacks 05Z4. -/
theorem exists_chart_universalHomeomorphism_of_isIntegralHom (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (huh : UniversalHomeomorphism B S hS f.hom)
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map j) := by
  have hrep : yoneda.relativelyRepresentable f.hom :=
    ((isIntegralHom_iff_representable B S hS f.hom X.2 Y.2).1 hf).1
  have hP := (presheaf_universalHomeomorphism_iff B S hS X.2 Y.2 hrep).2 huh
  exact ⟨hrep.pullback ζ, hrep.snd ζ, hrep.fst ζ, (hrep.isPullback ζ).flip,
    hP.2 ζ (hrep.fst ζ) (hrep.snd ζ) (hrep.isPullback ζ)⟩

end Chart

/-! ### Stacks 04DZ on the big fppf site -/

section Lift

/-- **Stacks 04DZ for objects of a big fppf site.** Let `j : W₀ ⟶ W` be a morphism of the big
fppf category over `S` whose underlying morphism of schemes is a universal homeomorphism, and let
`p` be an étale morphism from the scheme underlying an object `U` to the scheme underlying `W₀`.
Then `U` is the base change along `j` of an object of the category étale over `W`.

The lift is `Stacks.Etale.exists_etale_pullback_iso`; it lies in the site because it is étale over
`W` and homeomorphic to `U`, the projection of a base change along a universal homeomorphism
being a homeomorphism (`Stacks.Etale.contains_of_etale_of_isHomeomorph`). -/
@[sga "1 IX 4.10" "essential surjectivity", sga "4½ Th_finitude 2.7" "partial"]
theorem exists_bigFppfOver_etale_pullback_iso_of_universalHomeomorphism
    {W₀ W : BigFppfOver B S hS} (j : W₀ ⟶ W)
    [_root_.AlgebraicGeometry.UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map j)]
    (U : BigFppfOver B S hS)
    (p : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W₀)
    (hp : Etale p) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ W)
      (_ : Etale ((BigFppfOver.toScheme B S hS).map q))
      (e : pullback ((BigFppfOver.toScheme B S hS).map q)
          ((BigFppfOver.toScheme B S hS).map j) ≅ (BigFppfOver.toScheme B S hS).obj U),
      e.hom ≫ p = pullback.snd ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j) := by
  obtain ⟨V₀, q₀, hq₀, e, he⟩ :=
    Stacks.Etale.exists_etale_pullback_iso ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).obj U) p hp
  have h₁ : (pullback q₀ ((BigFppfOver.toScheme B S hS).map j) : Scheme.{u}) ≃ₜ V₀ :=
    (Stacks.Etale.isHomeomorph_pullbackFst ((BigFppfOver.toScheme B S hS).map j) q₀).homeomorph _
  have h₂ : (pullback q₀ ((BigFppfOver.toScheme B S hS).map j) : Scheme.{u}) ≃ₜ
      (BigFppfOver.toScheme B S hS).obj U := Scheme.Hom.homeomorph e.hom
  have hV₀ : B.Contains V₀ :=
    Stacks.Etale.contains_of_etale_of_isHomeomorph B q₀ hq₀ (h₁.symm.trans h₂)
      (Homeomorph.isHomeomorph _) U.left.2 W.left.2
  obtain ⟨q, hqmap⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := BigFppfOver.mk B S hS hV₀ (q₀ ≫ B.inclusion.map W.hom)) (Y := W) q₀ rfl
  refine ⟨BigFppfOver.mk B S hS hV₀ (q₀ ≫ B.inclusion.map W.hom), q, ?_⟩
  rw [hqmap]
  exact ⟨hq₀, e, he⟩

/-- **Stacks 04DZ on the site, in the cartesian form a lifted étale presentation asks for.** Let
`j : J ⟶ Z` be a morphism of objects of the site whose underlying morphism of schemes is a
universal homeomorphism and which exhibits `J` as the base change along `g` of a chart `ζ` of the
target, and let `k : U ⟶ J` be étale. Then `U` lifts to an object `V` of the site étale over `Z`,
and the lift is cartesian both over `j` inside the site and over `g` in presheaves. -/
theorem exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : F ⟶ G} {Z J U : BigFppfOver B S hS}
    (j : J ⟶ Z)
    [_root_.AlgebraicGeometry.UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map j)]
    (η : yoneda.obj J ⟶ F) (ζ : yoneda.obj Z ⟶ G) (hζ : IsEtale B S hS ζ)
    (hchart : IsPullback (yoneda.map j) η ζ g)
    (k : U ⟶ J)
    (hk : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k)) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ Z) (p : U ⟶ V),
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        IsEtale B S hS (yoneda.map q ≫ ζ) ∧
        IsPullback p k q j ∧
        IsPullback (yoneda.map p) (yoneda.map k ≫ η) (yoneda.map q ≫ ζ) g := by
  obtain ⟨V, q, hqE, e, he⟩ :=
    exists_bigFppfOver_etale_pullback_iso_of_universalHomeomorphism B S hS j U
      ((BigFppfOver.toScheme B S hS).map k) hk
  obtain ⟨p, hsite, hpres⟩ :=
    exists_isPullback_presheaf_of_iso_pullback_toScheme B S hS q j k η ζ hchart e he
  refine ⟨V, q, p, hqE, isEtale_comp B S hS ?_ hζ, hsite, hpres⟩
  exact (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).2
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqE)

end Lift

/-! ### Extension of presheaf morphisms across a universal homeomorphism -/

section Extension

variable {X Y : AlgebraicSpaces B S hS}

/-- **Two morphisms over `Y` into a space unramified over `Y` which agree after base change
along a surjective `f` are equal.** The projection of the base change is surjective on points,
so `AlgebraicGeometry.Space.eq_of_comp_eq_of_isSurjective` applies. -/
theorem hom_ext_presheaf_of_isSurjective (f : X ⟶ Y) (hsurj : IsSurjective B S hS f.hom)
    {F Gp H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hGp : IsAlgebraicSpace B S hS Gp)
    {v : F ⟶ Y.1} {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : Gp ⟶ Y.1) (hw : IsUnramified B S hS w) (α β : F ⟶ Gp)
    (hα : α ≫ w = v) (hβ : β ≫ w = v) (h : π ≫ α = π ≫ β) : α = β := by
  have hH : IsAlgebraicSpace B S hS H :=
    isAlgebraicSpace_of_isPullback hF X.2 Y.2.isSheaf Y.2.diagonal_representable hpb
  have hπ : IsSurjective B S hS π :=
    isSurjective_of_isPullback B S hS
      (p := (ObjectProperty.homMk q : (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ X))
      (q := (ObjectProperty.homMk π : (⟨H, hH⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩))
      (g := f) (f := (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y))
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hpb.flip) hsurj
  exact eq_of_comp_eq_of_isSurjective B S hS hGp Y.2 w hw α β (by rw [hα, hβ]) π hπ h

/-- **Extension of morphisms into a space étale over `Y`, at the level of presheaves, across a
morphism `f` along which base change is full.** Let `v : F ⟶ Y.1` and `w : Gp ⟶ Y.1` be étale
with `F` and `Gp` algebraic spaces, and let `π : H ⟶ F` be a base change of `f`. Every morphism
`H ⟶ Gp` over `Y` extends to a morphism `F ⟶ Gp` over `Y`. -/
theorem exists_hom_presheaf_of_full (f : X ⟶ Y)
    (hfull : (spacesBaseChange B S hS f).functor.Full)
    {F Gp H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hGp : IsAlgebraicSpace B S hS Gp)
    {v : F ⟶ Y.1} (hv : IsEtale B S hS v)
    {π : H ⟶ F} {q : H ⟶ X.1} (hpb : IsPullback π q v f.hom)
    (w : Gp ⟶ Y.1) (hw : IsEtale B S hS w)
    (d : H ⟶ Gp) (hd : d ≫ w = π ≫ v) :
    ∃ α : F ⟶ Gp, π ≫ α = d ∧ α ≫ w = v := by
  let D := spacesBaseChange B S hS f
  let V' : SpacesEtale B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk v : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ Y), hv⟩
  let V : SpacesEtale B S hS Y :=
    ⟨Over.mk (ObjectProperty.homMk w : (⟨Gp, hGp⟩ : AlgebraicSpaces B S hS) ⟶ Y), hw⟩
  have sqV' : IsPullback (D.projection.app V').hom ((D.functor.obj V').1.hom).hom v f.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V')
  have sqV : IsPullback (D.projection.app V).hom ((D.functor.obj V).1.hom).hom w f.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V)
  -- The given cartesian square and the canonical one are isomorphic over their cospan.
  obtain ⟨θ, hθiso, hθ⟩ : ∃ θ : H ⟶ (D.functor.obj V').1.left.1,
      IsIso θ ∧ θ ≫ (D.projection.app V').hom = π :=
    ⟨(hpb.isoIsPullback _ _ sqV').hom, inferInstance,
      IsPullback.isoIsPullback_hom_fst _ _ hpb sqV'⟩
  have := hθiso
  -- `d` and the projection of `H` assemble into a morphism of the two base changes.
  have hcond : (inv θ ≫ d) ≫ w = ((D.functor.obj V').1.hom).hom ≫ f.hom := by
    rw [Category.assoc, hd, ← hθ, Category.assoc, IsIso.inv_hom_id_assoc]
    exact sqV'.w
  obtain ⟨cpre, hcpre₁, hcpre₂⟩ : ∃ cpre : (D.functor.obj V').1.left.1 ⟶
        (D.functor.obj V).1.left.1,
      cpre ≫ (D.projection.app V).hom = inv θ ≫ d ∧
        cpre ≫ ((D.functor.obj V).1.hom).hom = ((D.functor.obj V').1.hom).hom :=
    ⟨sqV.lift _ _ hcond, sqV.lift_fst _ _ hcond, sqV.lift_snd _ _ hcond⟩
  have hc : (ObjectProperty.homMk cpre : (D.functor.obj V').1.left ⟶ (D.functor.obj V).1.left) ≫
      (D.functor.obj V).1.hom = (D.functor.obj V').1.hom :=
    ObjectProperty.hom_ext _ hcpre₂
  -- Fullness descends it.
  obtain ⟨a, ha⟩ := hfull.map_surjective
    (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk cpre) hc))
  have hca : (D.functor.map a).hom.left.hom = cpre := by
    rw [ha]
    rfl
  have hnat : (D.projection.app V').hom ≫ a.hom.left.hom =
      (D.functor.map a).hom.left.hom ≫ (D.projection.app V).hom :=
    (congrArg (fun k ↦ k.hom) (D.projection.naturality a)).symm
  refine ⟨a.hom.left.hom, ?_, congrArg (fun k ↦ k.hom) (Over.w a.hom)⟩
  calc π ≫ a.hom.left.hom
      = (θ ≫ (D.projection.app V').hom) ≫ a.hom.left.hom := by rw [hθ]
    _ = θ ≫ cpre ≫ (D.projection.app V).hom := by rw [Category.assoc, hnat, hca]
    _ = θ ≫ inv θ ≫ d := by rw [hcpre₁]
    _ = d := by rw [IsIso.hom_inv_id_assoc]

end Extension

/-! ### Lifted étale presentations across an integral universal homeomorphism -/

section Presentation

variable {X Y : AlgebraicSpaces B S hS}

/-- **The charts and the two étale lifts of a lifted étale presentation exist across an integral
universal homeomorphism.** For `f : X ⟶ Y` integral and a universal homeomorphism, and an object
`C` of the spaces-étale site of `X`, there are objects `V`, `W`, `U`, `R` of the site, structure
morphisms `v`, `w` making `V` and `W` étale over `Y`, a surjective étale chart `c` of `C` by `U`
with kernel pair `(s, t)` by `R`, and projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R`
as the base changes of `V` and of `W` along `f`.

An étale chart `ζ` of `Y` restricts `f` to a universal homeomorphism of schemes `j : J ⟶ Z`
(`AlgebraicGeometry.Space.exists_chart_universalHomeomorphism_of_isIntegralHom`); an étale chart
of `C` base changed to `J` is `U`, its kernel pair is `R`, and both lift across `j` by Stacks 04DZ
(`AlgebraicGeometry.Space.exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism`). -/
theorem exists_liftedEtalePresentation_charts_of_isIntegralHom (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (huh : UniversalHomeomorphism B S hS f.hom)
    (C : SpacesEtale B S hS X) :
    ∃ (V W U R : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y.1) (w : yoneda.obj W ⟶ Y.1)
        (c : yoneda.obj U ⟶ C.1.left.1) (a : U ⟶ V) (b : R ⟶ W) (s t : R ⟶ U),
      IsEtale B S hS v ∧ IsEtale B S hS w ∧ IsEtale B S hS c ∧
        (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf c ∧
        IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom ∧
        IsPullback (yoneda.map t) (yoneda.map s) c c ∧
        IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom := by
  -- An étale chart of `Y`, and the restriction of `f` to it.
  obtain ⟨Z, ζ, hζS, hζE⟩ := Y.2.exists_atlas
  have hζI : IsEtale B S hS ζ := isEtale_of_presheaf_etale B S hS hζE
  obtain ⟨J, j, η, hchart, hjuh⟩ :=
    exists_chart_universalHomeomorphism_of_isIntegralHom B S hS f hf huh Z ζ
  have : _root_.AlgebraicGeometry.UniversalHomeomorphism ((BigFppfOver.toScheme B S hS).map j) :=
    hjuh
  have hηE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf η :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hchart hζE
  have hηS : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf η :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hchart hζS
  -- An étale chart of `C`, and its base change to the chart of `X`.
  obtain ⟨U', c', hc'S, hc'E⟩ := C.1.left.2.exists_atlas
  have hg₀E : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c' ≫ C.1.hom.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hc'E) C.2)
  obtain ⟨U, κ, m, hUpb⟩ :
      ∃ (U : BigFppfOver B S hS) (κ : yoneda.obj U ⟶ yoneda.obj J) (m : U ⟶ U'),
        IsPullback κ (yoneda.map m) η (c' ≫ C.1.hom.hom) :=
    ⟨_, _, _, hηE.rep.isPullback (c' ≫ C.1.hom.hom)⟩
  obtain ⟨k, hkmap⟩ := yoneda.map_surjective κ
  rw [← hkmap] at hUpb
  have hmE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hUpb hηE
  have hmS : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hUpb hηS
  have hkE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hUpb.flip hg₀E)
  -- The chart of `C` through the base change, and its kernel pair.
  have hcI : IsEtale B S hS (yoneda.map m ≫ c') :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hmE)
      (isEtale_of_presheaf_etale B S hS hc'E)
  have hcE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m ≫ c') :=
    presheaf_etale_of_isEtale B S hS hcI
  have hcS : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map m ≫ c') := by
    refine (presheafSurjective_iff_isSurjective_yoneda B S hS C.1.left.1 C.1.left.2 U _).2 ?_
    have h₁ := isSurjective_of_presheafSurjective B S hS _ hmS
    have h₂ := isSurjective_of_presheafSurjective B S hS _ hc'S
    change Function.Surjective (pointsMap B S hS (yoneda.obj U) (yoneda.map m ≫ c'))
    rw [pointsMap_comp]
    exact h₂.comp h₁
  have hcw : yoneda.map k ≫ η = (yoneda.map m ≫ c') ≫ C.1.hom.hom := by
    rw [Category.assoc]
    exact hUpb.w
  obtain ⟨R, s₀, t₀, hker⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map m ≫ c') (yoneda.map m ≫ c') :=
    ⟨hcE.rep.pullback _, yoneda.preimage (hcE.rep.fst _), hcE.rep.snd _, by
      simpa only [yoneda.map_preimage] using hcE.rep.isPullback _⟩
  have htE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (s₀ ≫ k)) := by
    have h₁ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s₀) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ s₀).1
        ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hker.flip hcE)
    rw [Functor.map_comp]
    infer_instance
  -- The two étale lifts across the chart-level universal homeomorphism.
  obtain ⟨V, q, a, -, hvE, -, hpresA⟩ :=
    exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism B S hS j η ζ hζI hchart k hkE
  obtain ⟨W, qW, b, -, hwE, -, hpresB⟩ :=
    exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism B S hS j η ζ hζI hchart
      (s₀ ≫ k) htE
  refine ⟨V, W, U, R, yoneda.map q ≫ ζ, yoneda.map qW ≫ ζ, yoneda.map m ≫ c', a, b, t₀, s₀,
    hvE, hwE, hcI, hcS, ?_, hker, ?_⟩
  · rw [← hcw]
    exact hpresA
  · rw [Functor.map_comp, Category.assoc, hcw] at hpresB
    simp only [Category.assoc] at hpresB ⊢
    exact hpresB

/-- **The two descended projections of a lifted kernel pair are jointly monic in the site.**
Two morphisms into `W` agreeing after `k₁` and after `k₂` are compared through both components
of `U = V ×_Y X`, and agree after base change along the surjective `f`. -/
theorem eq_of_comp_eq_of_liftedKernelPair (f : X ⟶ Y) (hsurj : IsSurjective B S hS f.hom)
    (C : SpacesEtale B S hS X) {V W U R : BigFppfOver B S hS} {v : yoneda.obj V ⟶ Y.1}
    {w : yoneda.obj W ⟶ Y.1} {c : yoneda.obj U ⟶ C.1.left.1} {a : U ⟶ V} {b : R ⟶ W}
    {s t : R ⟶ U} {k₁ k₂ : W ⟶ V} (hwU : IsUnramified B S hS w)
    (hA : IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom)
    (hC : IsPullback (yoneda.map t) (yoneda.map s) c c)
    (hB : IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom)
    (hbk₁ : yoneda.map b ≫ yoneda.map k₁ = yoneda.map t ≫ yoneda.map a)
    (hbk₂ : yoneda.map b ≫ yoneda.map k₂ = yoneda.map s ≫ yoneda.map a)
    (hk₁ : yoneda.map k₁ ≫ v = w) {T : BigFppfOver B S hS} (x y : T ⟶ W)
    (h₂ : x ≫ k₂ = y ≫ k₂) (h₁ : x ≫ k₁ = y ≫ k₁) : x = y := by
  apply yoneda.map_injective
  have hyw : yoneda.map y ≫ w = yoneda.map x ≫ w := by
    rw [← hk₁]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [h₁]
  have hQ : IsPullback (pullback.fst (yoneda.map x ≫ w) f.hom)
      (pullback.snd (yoneda.map x ≫ w) f.hom) (yoneda.map x ≫ w) f.hom :=
    IsPullback.of_hasPullback _ _
  set πQ := pullback.fst (yoneda.map x ≫ w) f.hom
  set qQ := pullback.snd (yoneda.map x ≫ w) f.hom
  have hxQ : (πQ ≫ yoneda.map x) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc]
    exact hQ.w
  have hyQ : (πQ ≫ yoneda.map y) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc, hyw]
    exact hQ.w
  obtain ⟨ξx, hξx, hξx'⟩ : ∃ ξ : pullback (yoneda.map x ≫ w) f.hom ⟶ yoneda.obj R,
      ξ ≫ yoneda.map b = πQ ≫ yoneda.map x ∧ ξ ≫ yoneda.map t ≫ c ≫ C.1.hom.hom = qQ :=
    ⟨hB.lift _ _ hxQ, hB.lift_fst _ _ hxQ, hB.lift_snd _ _ hxQ⟩
  obtain ⟨ξy, hξy, hξy'⟩ : ∃ ξ : pullback (yoneda.map x ≫ w) f.hom ⟶ yoneda.obj R,
      ξ ≫ yoneda.map b = πQ ≫ yoneda.map y ∧ ξ ≫ yoneda.map t ≫ c ≫ C.1.hom.hom = qQ :=
    ⟨hB.lift _ _ hyQ, hB.lift_fst _ _ hyQ, hB.lift_snd _ _ hyQ⟩
  have hkey : ∀ (k : W ⟶ V) (p : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      yoneda.map p ≫ c = yoneda.map t ≫ c → x ≫ k = y ≫ k →
      ξx ≫ yoneda.map p = ξy ≫ yoneda.map p := by
    intro k p hkp hpc hxy
    refine hA.hom_ext ?_ ?_
    · calc (ξx ≫ yoneda.map p) ≫ yoneda.map a
          = (ξx ≫ yoneda.map b) ≫ yoneda.map k := by
            simp only [Category.assoc, hkp]
        _ = (πQ ≫ yoneda.map x) ≫ yoneda.map k := by rw [hξx]
        _ = (πQ ≫ yoneda.map y) ≫ yoneda.map k := by
            simp only [Category.assoc, ← Functor.map_comp]
            rw [hxy]
        _ = (ξy ≫ yoneda.map b) ≫ yoneda.map k := by rw [hξy]
        _ = (ξy ≫ yoneda.map p) ≫ yoneda.map a := by
            simp only [Category.assoc, hkp]
    · rw [Category.assoc, ← Category.assoc (yoneda.map p), hpc, Category.assoc, hξx',
        Category.assoc, ← Category.assoc (yoneda.map p), hpc, Category.assoc, hξy']
  have hξ : ξx = ξy := hC.hom_ext (hkey k₁ t hbk₁ rfl h₁) (hkey k₂ s hbk₂ hC.w.symm h₂)
  refine hom_ext_presheaf_of_isSurjective B S hS f hsurj
    (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS W) hQ w hwU
    (yoneda.map x) (yoneda.map y) rfl hyw ?_
  rw [← hξx, ← hξy, hξ]

/-- **Every object of the spaces-étale site of `X` admits a lifted étale presentation across an
integral, universally injective and surjective `f : X ⟶ Y`.**

This is the source's step: the two projections of the kernel pair of a chart descend by fullness
of base change (`AlgebraicGeometry.Space.exists_hom_presheaf_of_full`), and every identity needed
to see that the descended pair is an equivalence relation is checked after base change, by
faithfulness (`AlgebraicGeometry.Space.hom_ext_presheaf_of_isSurjective`). -/
theorem nonempty_liftedEtalePresentation_of_isIntegralHom (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (hinj : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (C : SpacesEtale B S hS X) :
    Nonempty (LiftedEtalePresentation B S hS f C) := by
  have huh : UniversalHomeomorphism B S hS f.hom :=
    universalHomeomorphism_of_isIntegralHom B S hS X.2 Y.2 hf hinj hsurj
  have hfull := full_spacesBaseChange_of_universalHomeomorphism B S hS f huh
  obtain ⟨V, W, U, R, v, w, c, a, b, s, t, hv, hw, hc, hcS, hA, hC, hB⟩ :=
    exists_liftedEtalePresentation_charts_of_isIntegralHom B S hS f hf huh C
  have hVas := isAlgebraicSpace_yoneda B S hS V
  have hWas := isAlgebraicSpace_yoneda B S hS W
  have hvU : IsUnramified B S hS v := isUnramified_of_isEtale B S hS hv
  have hwU : IsUnramified B S hS w := isUnramified_of_isEtale B S hS hw
  -- The two maps of the relation, the descents of `t ≫ a` and of `s ≫ a` by fullness.
  have hd₁ : (yoneda.map t ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [Category.assoc]
  obtain ⟨κ₁, hκ₁b, hκ₁v⟩ := exists_hom_presheaf_of_full B S hS f hfull
    hWas hVas hw hB v hv (yoneda.map t ≫ yoneda.map a) hd₁
  have hd₂ : (yoneda.map s ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [← Category.assoc]
    rw [← hC.w]
  obtain ⟨κ₂, hκ₂b, hκ₂v⟩ := exists_hom_presheaf_of_full B S hS f hfull
    hWas hVas hw hB v hv (yoneda.map s ≫ yoneda.map a) hd₂
  obtain ⟨k₁, hk₁⟩ := yoneda.map_surjective κ₁
  obtain ⟨k₂, hk₂⟩ := yoneda.map_surjective κ₂
  rw [← hk₁] at hκ₁b hκ₁v
  rw [← hk₂] at hκ₂b hκ₂v
  have hbk₁ : b ≫ k₁ = t ≫ a :=
    yoneda.map_injective (by simpa only [Functor.map_comp] using hκ₁b)
  have hbk₂ : b ≫ k₂ = s ≫ a :=
    yoneda.map_injective (by simpa only [Functor.map_comp] using hκ₂b)
  -- `R` is the fibre product of `W` and of `U` over `V`.
  have hPB : IsPullback (yoneda.map b) (yoneda.map t) (yoneda.map k₁) (yoneda.map a) := by
    refine IsPullback.of_bot ?_ ?_ hA
    · rw [hκ₁v]
      exact hB
    · rw [← Functor.map_comp, ← Functor.map_comp, hbk₁]
  have hbk₂' : yoneda.map b ≫ yoneda.map k₂ = yoneda.map s ≫ yoneda.map a := by
    rw [← Functor.map_comp, ← Functor.map_comp, hbk₂]
  -- The two maps of the relation are étale, by Stacks 03MJ on charts.
  have hwP : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w :=
    presheaf_etale_of_isEtale B S hS hw
  have hvP : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v :=
    presheaf_etale_of_isEtale B S hS hv
  have hk₁E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₁) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₁v
  have hk₂E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₂) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₂v
  -- The transitivity cone `W ×_V W` is étale over `Y`, which is what lifting from it needs.
  have hfstPB : IsPullback (yoneda.map (pullback.fst k₁ k₂)) (yoneda.map (pullback.snd k₁ k₂))
      (yoneda.map k₁) (yoneda.map k₂) := (IsPullback.of_hasPullback k₁ k₂).map yoneda
  have hfstI : IsEtale B S hS (yoneda.map (pullback.fst k₁ k₂) ≫ w) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hfstPB.flip
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k₂).2 hk₂E))) hw
  -- Reflexivity, symmetry and transitivity of the kernel pair upstairs.
  obtain ⟨ρ, hρt, hρs⟩ : ∃ ρ : U ⟶ R, ρ ≫ t = 𝟙 U ∧ ρ ≫ s = 𝟙 U := by
    refine ⟨yoneda.preimage (hC.lift (𝟙 _) (𝟙 _) rfl), yoneda.map_injective ?_,
      yoneda.map_injective ?_⟩
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_fst, CategoryTheory.Functor.map_id]
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_snd, CategoryTheory.Functor.map_id]
  obtain ⟨μ, hμt, hμs⟩ : ∃ μ : R ⟶ R, μ ≫ t = s ∧ μ ≫ s = t := by
    refine ⟨yoneda.preimage (hC.lift (yoneda.map s) (yoneda.map t) hC.w.symm),
      yoneda.map_injective ?_, yoneda.map_injective ?_⟩
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_fst]
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_snd]
  -- Reflexivity downstairs.
  have hdr : yoneda.map (ρ ≫ b) ≫ w = yoneda.map a ≫ v := by
    rw [Functor.map_comp, Category.assoc, hB.w, hA.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hρt, CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨rr₀, hr₀a, hr₀w⟩ := exists_hom_presheaf_of_full B S hS f hfull
    hVas hWas hv hA w hw (yoneda.map (ρ ≫ b)) hdr
  obtain ⟨rr, hrr⟩ := yoneda.map_surjective rr₀
  rw [← hrr] at hr₀a hr₀w
  have hrefl : ∀ (k : W ⟶ V) (p : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ρ ≫ p = 𝟙 U → yoneda.map k ≫ v = w → rr ≫ k = 𝟙 V := by
    intro k p hkp hρp hkv
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj hVas hVas hA v hvU
      (yoneda.map (rr ≫ k)) (yoneda.map (𝟙 V)) ?_ ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hr₀w
    · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    · rw [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, ← Category.assoc,
        hr₀a]
      simp only [Functor.map_comp, Category.assoc, hkp]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hρp, Category.id_comp]
  -- Symmetry downstairs.
  have hds : yoneda.map (μ ≫ b) ≫ w = yoneda.map b ≫ w := by
    rw [Functor.map_comp, Category.assoc, hB.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hμt, hC.w]
  obtain ⟨σ₀, hσ₀b, hσ₀w⟩ := exists_hom_presheaf_of_full B S hS f hfull
    hWas hWas hw hB w hw (yoneda.map (μ ≫ b)) hds
  obtain ⟨σ, hσ⟩ := yoneda.map_surjective σ₀
  rw [← hσ] at hσ₀b hσ₀w
  have hsymm : ∀ (k k' : W ⟶ V) (p p' : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      yoneda.map b ≫ yoneda.map k' = yoneda.map p' ≫ yoneda.map a →
      μ ≫ p = p' → yoneda.map k ≫ v = w → yoneda.map k' ≫ v = w → σ ≫ k = k' := by
    intro k k' p p' hkp hkp' hμp hkv hkv'
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj hWas hVas hB v hvU
      (yoneda.map (σ ≫ k)) (yoneda.map k') ?_ hkv' ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hσ₀w
    · rw [Functor.map_comp, ← Category.assoc, hσ₀b]
      simp only [Functor.map_comp, Category.assoc, hkp, hkp']
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hμp]
  -- Transitivity downstairs.
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hQ : IsPullback (pullback.fst (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom)
      (pullback.snd (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom)
      (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom := IsPullback.of_hasPullback _ _
  set πQ := pullback.fst (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom
  set qQ := pullback.snd (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom
  have hπ₂w : yoneda.map (pullback.snd k₁ k₂) ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w :=
    calc yoneda.map (pullback.snd k₁ k₂) ≫ w
        = yoneda.map (pullback.snd k₁ k₂ ≫ k₂) ≫ v := by
          rw [← hκ₂v, Functor.map_comp, Category.assoc]
      _ = yoneda.map (pullback.fst k₁ k₂ ≫ k₁) ≫ v := by rw [← pullback.condition]
      _ = yoneda.map (pullback.fst k₁ k₂) ≫ w := by
          rw [← hκ₁v, Functor.map_comp, Category.assoc]
  have hQ₁ : (πQ ≫ yoneda.map (pullback.fst k₁ k₂)) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc]
    exact hQ.w
  have hQ₂ : (πQ ≫ yoneda.map (pullback.snd k₁ k₂)) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc, hπ₂w]
    exact hQ.w
  obtain ⟨ζ₁, hζ₁b, hζ₁x⟩ : ∃ ζ : pullback (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom ⟶
        yoneda.obj R,
      ζ ≫ yoneda.map b = πQ ≫ yoneda.map (pullback.fst k₁ k₂) ∧
        ζ ≫ (yoneda.map t ≫ c ≫ C.1.hom.hom) = qQ :=
    ⟨hB.lift _ _ hQ₁, hB.lift_fst _ _ hQ₁, hB.lift_snd _ _ hQ₁⟩
  obtain ⟨ζ₂, hζ₂b, hζ₂x⟩ : ∃ ζ : pullback (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom ⟶
        yoneda.obj R,
      ζ ≫ yoneda.map b = πQ ≫ yoneda.map (pullback.snd k₁ k₂) ∧
        ζ ≫ (yoneda.map t ≫ c ≫ C.1.hom.hom) = qQ :=
    ⟨hB.lift _ _ hQ₂, hB.lift_fst _ _ hQ₂, hB.lift_snd _ _ hQ₂⟩
  have hcross : ζ₁ ≫ yoneda.map t = ζ₂ ≫ yoneda.map s := by
    refine hA.hom_ext ?_ ?_
    · calc (ζ₁ ≫ yoneda.map t) ≫ yoneda.map a
          = (ζ₁ ≫ yoneda.map b) ≫ yoneda.map k₁ := by simp only [Category.assoc, hPB.w]
        _ = πQ ≫ yoneda.map (pullback.fst k₁ k₂ ≫ k₁) := by
            rw [hζ₁b, Functor.map_comp, Category.assoc]
        _ = πQ ≫ yoneda.map (pullback.snd k₁ k₂ ≫ k₂) := by rw [pullback.condition]
        _ = (ζ₂ ≫ yoneda.map b) ≫ yoneda.map k₂ := by
            rw [hζ₂b, Functor.map_comp, Category.assoc]
        _ = (ζ₂ ≫ yoneda.map s) ≫ yoneda.map a := by simp only [Category.assoc, hbk₂']
    · rw [Category.assoc, hζ₁x, Category.assoc, ← Category.assoc (yoneda.map s), hC.w.symm,
        Category.assoc, hζ₂x]
  have hzc : (ζ₂ ≫ yoneda.map t) ≫ c = (ζ₁ ≫ yoneda.map s) ≫ c := by
    simp only [Category.assoc, ← hC.w]
    rw [← Category.assoc, ← Category.assoc, hcross]
    simp only [Category.assoc, hC.w]
  obtain ⟨ζ, hζt, hζs⟩ : ∃ ζ : pullback (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom ⟶
        yoneda.obj R,
      ζ ≫ yoneda.map t = ζ₂ ≫ yoneda.map t ∧ ζ ≫ yoneda.map s = ζ₁ ≫ yoneda.map s :=
    ⟨hC.lift _ _ hzc, hC.lift_fst _ _ hzc, hC.lift_snd _ _ hzc⟩
  have hζx : ζ ≫ yoneda.map t ≫ c ≫ C.1.hom.hom = qQ := by
    rw [← Category.assoc ζ (yoneda.map t) (c ≫ C.1.hom.hom), hζt, Category.assoc]
    exact hζ₂x
  have hdt : (ζ ≫ yoneda.map b) ≫ w = πQ ≫ yoneda.map (pullback.fst k₁ k₂) ≫ w := by
    rw [Category.assoc, hB.w, ← Category.assoc, hζx]
    exact hQ.w.symm
  obtain ⟨τ₀, hτ₀Q, hτ₀w⟩ := exists_hom_presheaf_of_full B S hS f hfull
    (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hWas hfstI hQ w hw
    (ζ ≫ yoneda.map b) hdt
  obtain ⟨τ, hτ⟩ := yoneda.map_surjective τ₀
  rw [← hτ] at hτ₀Q hτ₀w
  have htrans : ∀ (k : W ⟶ V) (p : R ⟶ U) (π : pullback k₁ k₂ ⟶ W)
      (ζ' : pullback (yoneda.map (pullback.fst k₁ k₂) ≫ w) f.hom ⟶ yoneda.obj R),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ζ ≫ yoneda.map p = ζ' ≫ yoneda.map p →
      ζ' ≫ yoneda.map b = πQ ≫ yoneda.map π →
      yoneda.map k ≫ v = w → yoneda.map π ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w →
      τ ≫ k = π ≫ k := by
    intro k p π ζ' hkp hζp hζ'b hkv hπw
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj
      (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hVas hQ v hvU
      (yoneda.map (τ ≫ k)) (yoneda.map (π ≫ k)) ?_ ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hτ₀w
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hπw
    · rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hτ₀Q]
      rw [← hζ'b]
      simp only [Category.assoc, hkp, reassoc_of% hζp]
  -- The equivalence relation inside the site.
  have esite : EquivalenceRelation k₂ k₁ :=
    { right_cancellation := fun _ x y h₂ h₁ ↦ eq_of_comp_eq_of_liftedKernelPair B S hS f hsurj C
        hwU hA hC hB hPB.w hbk₂' hκ₁v x y h₂ h₁
      r := rr
      reflexivity₁ := hrefl k₂ s hbk₂' hρs hκ₂v
      reflexivity₂ := hrefl k₁ t hPB.w hρt hκ₁v
      s := σ
      symmetry₁ := hsymm k₂ k₁ s t hbk₂' hPB.w hμs hκ₂v hκ₁v
      symmetry₂ := hsymm k₁ k₂ t s hPB.w hbk₂' hμt hκ₁v hκ₂v
      c := pullback.cone k₁ k₂
      isLimit := pullback.isLimit k₁ k₂
      t := τ
      transitivity₁ := htrans k₂ s (pullback.fst k₁ k₂) ζ₁ hbk₂' hζs hζ₁b hκ₂v rfl
      transitivity₂ := htrans k₁ t (pullback.snd k₁ k₂) ζ₂ hPB.w hζt hζ₂b hκ₁v hπ₂w }
  refine ⟨{
    V := V
    W := W
    U := U
    R := R
    v := v
    w := w
    isEtale_v := hv
    isEtale_w := hw
    k₁ := k₁
    k₂ := k₂
    comp_k₁ := hκ₁v
    comp_k₂ := hκ₂v
    c := c
    isEtale_c := hc
    surjective_c := hcS
    a := a
    b := b
    s := s
    t := t
    isPullback_a := hA
    isPullback_b := hPB
    comp_b_k₂ := hbk₂
    isPullback_c := hC
    isEtaleEquivalenceRelation := ?_ }⟩
  have htarget : (relation B S hS k₁ k₂).target = (Over.post B.inclusion).map k₂ :=
    prod.lift_fst _ _
  have hsource : (relation B S hS k₁ k₂).source = (Over.post B.inclusion).map k₁ :=
    prod.lift_snd _ _
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [htarget, hsource]
    exact isEquivalenceRelation_overPost_of_equivalenceRelation B S hS esite
  · rw [hsource]
    exact hk₁E
  · rw [htarget]
    exact hk₂E

end Presentation

/-! ### Stacks 05ZH -/

section Equivalence

variable {X Y : AlgebraicSpaces B S hS}

/-- **Essential surjectivity of base change along an integral, universally injective and
surjective morphism.** Every object of the spaces-étale site of `X` admits a lifted étale
presentation across `f`, and the quotient of such a presentation is an object of the spaces-étale
site of `Y` whose base change along `f` is the given object. -/
theorem essSurj_spacesBaseChange_of_isIntegralHom (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (hinj : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.EssSurj where
  mem_essImage C := by
    obtain ⟨P⟩ := nonempty_liftedEtalePresentation_of_isIntegralHom B S hS f hf hinj hsurj C
    exact mem_essImage_spacesBaseChange_of_liftedEtalePresentation B S hS P

/-- **Stacks 05ZH.** Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism
of algebraic spaces over `S`. Base change `V ↦ X ×_Y V` is an equivalence from the spaces-étale
site of `Y` to that of `X`.

Faithfulness is `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective`, fullness is
`AlgebraicGeometry.Space.full_spacesBaseChange_of_universalHomeomorphism` — `f` being a universal
homeomorphism by `AlgebraicGeometry.Space.universalHomeomorphism_of_isIntegralHom` — and essential
surjectivity is `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isIntegralHom`.

This is Stacks 05ZH in full; the tag is not registered
here. -/
theorem isEquivalence_spacesBaseChange_of_isIntegralHom (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) (hinj : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  let := full_spacesBaseChange_of_universalHomeomorphism B S hS f
    (universalHomeomorphism_of_isIntegralHom B S hS X.2 Y.2 hf hinj hsurj)
  let := faithful_spacesBaseChange_of_isSurjective B S hS f hsurj
  let := essSurj_spacesBaseChange_of_isIntegralHom B S hS f hf hinj hsurj
  ⟨inferInstance, inferInstance, inferInstance⟩

end Equivalence

end AlgebraicGeometry.Space

end
