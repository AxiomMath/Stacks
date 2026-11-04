module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionStageLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting

/-!
# The lifting property passes along a formally étale chart

Let `S` be a scheme contained in a big fppf site `B`, `f : V' ⟶ V` a morphism of the site whose
completion `V'_{/f⁻¹Z} ⟶ V_{/Z}` along a set `Z` of points of `V` is formally étale,
`g : V_{/Z} ⟶ W` a morphism of fppf sheaves, `ψ : W' ⟶ W` formally étale and
`G' : V'_{/f⁻¹Z} ⟶ W'` over `g`. If `g` has the lifting property at `f(v')`
(`AlgebraicGeometry.FormalSpace.LiftsAtCompletion`) and the residue field extension of `f` at
`v'` is finite, then `G'` has the lifting property at `v'`.

## Main results

* `AlgebraicGeometry.FormalSpace.liftsAtCompletion_of_formallyEtale`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section of the sheafified universe lift of a sheaf comes from a section of the sheaf. -/
theorem toSheafify_ambientRead {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G ⋙ uliftFunctor.{u + 1}))
    {U : BigFppfOver B S hS} (z : (Space.sheafifiedULift B S hS G).obj.obj (op U)) :
    ((BigFppfOver.topology B S hS).toSheafify (G ⋙ uliftFunctor.{u + 1})).app (op U)
      (ULift.up (ambientRead B S hS hG z)) = z :=
  congrArg (fun φ ↦ φ.app (op U) z) ((BigFppfOver.topology B S hS).isoSheafify hG).inv_hom_id

/-- A section of the completion of a represented sheaf over `T'` whose restriction along
`i : T ⟶ T'` is the section given by `a : T ⟶ V'` is the section given by some `x : T' ⟶ V'`
restricting to `a`. -/
theorem exists_presheafSection_eq_of_map_eq {V' T T' : BigFppfOver B S hS}
    {Z' : Set (Space.points B S hS (yoneda.obj V'))} (i : T ⟶ T')
    (wτ : (Space.completionSheaf B S hS (yoneda.obj V') Z').obj.obj (op T')) (a : T ⟶ V')
    (ha : Space.HasImageIn B S hS (yoneda.obj V') Z' T a)
    (hw : (Space.completionSheaf B S hS (yoneda.obj V') Z').obj.map i.op wτ =
      presheafSection (F := yoneda.obj V') B S hS a ha) :
    ∃ (x : T' ⟶ V') (hx : Space.HasImageIn B S hS (yoneda.obj V') Z' T' x),
      wτ = presheafSection (F := yoneda.obj V') B S hS x hx ∧ i ≫ x = a := by
  have hV'u : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj V' ⋙ uliftFunctor.{u + 1}) :=
    (upliftedSheaf (yoneda.obj V') (isAlgebraicSpace_yoneda B S hS V')).property
  obtain ⟨x, hx⟩ : ∃ x : T' ⟶ V', (Space.completionSheafInclusion B S hS (yoneda.obj V') Z').hom.app
      (op T') wτ = ((BigFppfOver.topology B S hS).toSheafify
        (yoneda.obj V' ⋙ uliftFunctor.{u + 1})).app (op T') (ULift.up x) :=
    ⟨_, (toSheafify_ambientRead B S hS hV'u _).symm⟩
  obtain ⟨hxI, hwx⟩ := exists_presheafSection_eq_of_inclusion B S hS
    (isAlgebraicSpace_yoneda B S hS V').isSheaf hV'u wτ x hx
  have hix' : Space.HasImageIn B S hS (yoneda.obj V') Z' T ((yoneda.obj V').map i.op x) :=
    (Space.completionSubfunctor B S hS (yoneda.obj V') _).map i.op (a := ULift.up x) hxI
  refine ⟨x, hxI, hwx, ?_⟩
  have hsec : presheafSection (F := yoneda.obj V') B S hS ((yoneda.obj V').map i.op x) hix' =
      presheafSection (F := yoneda.obj V') B S hS a ha := by
    rw [← hw, hwx]
    exact (presheafSection_map (F := yoneda.obj V') (TF := Z') B S hS i x hxI hix').symm
  have h := eq_of_presheafSection_eq B S hS hV'u hix' ha hsec
  rwa [yoneda_obj_map, Quiver.Hom.unop_op] at h

/-- Two sections over `T'` of the source of a formally étale transformation agree if their
restrictions along a square-zero closed immersion `i : T ⟶ T'` and their images agree. -/
private theorem eq_of_map_eq_of_formallyEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {a : F ⟶ G} (ha : Space.FormallyEtale a) {T T' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) {z₁ z₂ : F.obj (op T')}
    (h₁ : F.map i.op z₁ = F.map i.op z₂) (h₂ : a.app (op T') z₁ = a.app (op T') z₂) :
    z₁ = z₂ :=
  (ha T T' inferInstance inferInstance i hi (F.map i.op z₂) (a.app _ z₂)
    (NatTrans.naturality_apply a i.op z₂)).unique ⟨h₁, h₂⟩ ⟨rfl, rfl⟩

/-- If `c ≫ g = G' ≫ ψ` with `ψ` formally étale, a section `z` of `W'` over `T'` agreeing with
`G' w` after restriction along a square-zero closed immersion `i : T ⟶ T'` and with
`g (c w)` after applying `ψ` is `G' w`. -/
private theorem eq_of_comp_eq_of_formallyEtale {X Y W W' : FppfSheaf B S hS} (c : X ⟶ Y)
    (g : Y ⟶ W) (ψ : W' ⟶ W) (G' : X ⟶ W') (hw : c ≫ g = G' ≫ ψ) (hψf : Space.FormallyEtale ψ.hom)
    {T T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) {w : X.obj.obj (op T')}
    {z : W'.obj.obj (op T')} (h₁ : W'.obj.map i.op (G'.hom.app _ w) = W'.obj.map i.op z)
    (h₂ : g.hom.app _ (c.hom.app _ w) = ψ.hom.app _ z) : G'.hom.app _ w = z :=
  eq_of_map_eq_of_formallyEtale B S hS hψf i hi h₁ (by
    rw [← h₂]
    exact (congrArg (fun k => k.hom.app (op T') w) hw).symm)

/-- The morphism `Spec D ⟶ Spec D'` induced by a small extension `φ : D' ⟶ D`, as a morphism of
the site over `S`, is a square-zero closed immersion. -/
private theorem isSquareZeroClosedImmersion_affineOverHom_specMap {D' D : CommRingCat.{u}}
    (φ : D' ⟶ D) (hφ : InfinitesimalLifting.IsSmallExtension φ) (hD : B.Contains (Spec (.of D)))
    (hD' : B.Contains (Spec (.of D'))) (s : Spec (.of D') ⟶ S) :
    Space.IsSquareZeroClosedImmersion B S hS (affineOverHom B S hS hD (Spec.map φ ≫ s)
      (V := affineOver B S hS hD' s) (Spec.map φ) rfl) := by
  obtain ⟨-, -, hsurj, hker⟩ := InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ
  exact Space.isSquareZeroClosedImmersion_of_specMap B S hS φ hsurj hker _ _ _ (Iso.refl _)
    (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- If the completion `V'_{/f⁻¹Z} ⟶ V_{/Z}` of `f : V' ⟶ V` is formally étale, a square
`i ≫ b = a ≫ f` against a square-zero closed immersion `i : T ⟶ T'` of affines, with `a` and `b`
in the completions, lifts to a morphism `x : T' ⟶ V'` into the completion with `i ≫ x = a`. -/
private theorem exists_completion_lift_of_formallyEtale {V' V T T' : BigFppfOver B S hS}
    (f : V' ⟶ V) (Z : Set (Space.points B S hS (yoneda.obj V)))
    (hcf : Space.FormallyEtale (Space.completionSheafMap B S hS (yoneda.map f) Z).hom)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) (a : T ⟶ V')
    (ha : Space.HasImageIn B S hS (yoneda.obj V')
      (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z) T a)
    (b : T' ⟶ V) (hb : Space.HasImageIn B S hS (yoneda.obj V) Z T' b)
    (hab : i ≫ b = a ≫ f) :
    ∃ (w : (Space.completionSheaf B S hS (yoneda.obj V')
        (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z)).obj.obj (op T'))
      (x : T' ⟶ V') (hx : Space.HasImageIn B S hS (yoneda.obj V')
        (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z) T' x),
      (Space.completionSheaf B S hS (yoneda.obj V')
        (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z)).obj.map i.op w =
          presheafSection B S hS a ha ∧
      (Space.completionSheafMap B S hS (yoneda.map f) Z).hom.app (op T') w =
          presheafSection B S hS b hb ∧
      w = presheafSection B S hS x hx ∧ i ≫ x = a := by
  have ha' := (hasImageIn_preimage_iff B S hS (yoneda.map f) Z _ _).mp ha
  have hib : Space.HasImageIn B S hS (yoneda.obj V) Z T ((yoneda.obj V).map i.op b) :=
    (Space.completionSubfunctor B S hS (yoneda.obj V) Z).map i.op (a := ULift.up b) hb
  have hsec : ∀ y (hy : Space.HasImageIn B S hS (yoneda.obj V) Z T y),
      y = (yoneda.obj V).map i.op b →
        presheafSection B S hS y hy = presheafSection B S hS _ hib := by
    rintro _ _ rfl
    rfl
  obtain ⟨w, ⟨hw₁, hw₂⟩, -⟩ := hcf T T' inferInstance inferInstance i hi
    (presheafSection B S hS a ha) (presheafSection B S hS b hb)
    ((completionSheafMap_presheafSection B S hS (yoneda.map f) Z a ha ha').trans
      ((hsec _ ha' (by simpa using hab.symm)).trans (presheafSection_map B S hS i _ hb hib).symm))
  obtain ⟨x, hx, hwx, hix⟩ := exists_presheafSection_eq_of_map_eq B S hS i w a ha hw₁
  exact ⟨w, x, hx, hw₁, hw₂, hwx, hix⟩

/-- **The lifting property passes along a formally étale chart.** Let `f : V' ⟶ V` have formally
étale completion `V'_{/f⁻¹Z} ⟶ V_{/Z}`, let `ψ : W' ⟶ W` be formally étale and let
`G' : V'_{/f⁻¹Z} ⟶ W'` lie over `g : V_{/Z} ⟶ W`. Then `G'` has the lifting property at every
point `v'` at which `f` has finite residue field extension and `g` has the lifting property at
`f(v')`: a lifting problem for `G'` pushes down to one for `g`, whose solution lifts uniquely to
`V'_{/f⁻¹Z}`, and maps to the given section of `W'` by uniqueness of lifts along `ψ`. -/
theorem liftsAtCompletion_of_formallyEtale {V' V : BigFppfOver B S hS} (f : V' ⟶ V)
    (Z : Set (Space.points B S hS (yoneda.obj V))) {W W' : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W) (ψ : W' ⟶ W)
    (G' : Space.completionSheaf B S hS (yoneda.obj V')
      (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z) ⟶ W')
    (hw : Space.completionSheafMap B S hS (yoneda.map f) Z ≫ g = G' ≫ ψ)
    (hcf : Space.FormallyEtale (Space.completionSheafMap B S hS (yoneda.map f) Z).hom)
    (hψf : Space.FormallyEtale ψ.hom)
    (v' : ((Over.post B.inclusion).obj V' : Over S).left)
    (hfin : ((((Over.post B.inclusion).map f).left).residueFieldMap v').hom.Finite)
    (hlift : LiftsAtCompletion B S hS V Z W g (((Over.post B.inclusion).map f).left v')) :
    LiftsAtCompletion B S hS V' (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z)
      W' G' v' := by
  classical
  intro D' D φ hφ hloc hD hD' s α hα hpt hfinα ha z hz
  have := hloc
  subst hpt
  let fS : ((Over.post B.inclusion).obj V' : Over S).left ⟶
      ((Over.post B.inclusion).obj V : Over S).left := ((Over.post B.inclusion).map f).left
  have hα' : (α ≫ fS) ≫ ((Over.post B.inclusion).obj V : Over S).hom = Spec.map φ ≫ s :=
    (Category.assoc _ _ _).trans
      ((congrArg (α ≫ ·) (Over.w ((Over.post B.inclusion).map f))).trans hα)
  have hfin' : ((α ≫ fS).residueFieldMap (IsLocalRing.closedPoint D)).hom.Finite := by
    rw [Scheme.residueFieldMap_comp α fS (IsLocalRing.closedPoint D)]
    exact hfinα.comp hfin
  let T' := affineOver B S hS hD' s
  let T := affineOver B S hS hD (Spec.map φ ≫ s)
  let i : T ⟶ T' := affineOverHom B S hS hD (Spec.map φ ≫ s) (V := T') (Spec.map φ) rfl
  have ha' := (hasImageIn_preimage_iff B S hS (yoneda.map f) Z _ _).mp ha
  have hcs := completionSheafMap_presheafSection B S hS (yoneda.map f) Z
    (affineOverHom B S hS hD _ α hα) ha ha'
  have hz' : W.obj.map i.op (ψ.hom.app _ z) = g.hom.app _ (presheafSection B S hS _ ha') := by
    refine (NatTrans.naturality_apply ψ.hom i.op z).symm.trans ?_
    refine (congrArg (ψ.hom.app _) hz).trans ?_
    refine (congrArg (fun k => k.hom.app _ (presheafSection B S hS _ ha)) hw).symm.trans ?_
    exact congrArg (g.hom.app _) hcs
  obtain ⟨β, hβ, hb, h1, h2⟩ := hlift φ hφ hD hD' s (α ≫ fS) hα' rfl hfin' ha' _ hz'
  -- the thickening `Spec D ⟶ Spec D'`
  have hi : Space.IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_affineOverHom_specMap B S hS φ hφ hD hD' s
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := inferInstanceAs (IsAffine (Spec _))
  -- the lift of `β` to the completion of `V'`
  have hib : i ≫ affineOverHom B S hS hD' s β hβ = affineOverHom B S hS hD _ α hα ≫ f :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ h1)
  obtain ⟨wτ, x, hxI, hwτ1, hwτ2, hwx, hix⟩ :=
    exists_completion_lift_of_formallyEtale B S hS f Z hcf i hi _ ha _ hb hib
  let β' : Spec (.of D') ⟶ ((Over.post B.inclusion).obj V' : Over S).left :=
    (BigFppfOver.toScheme B S hS).map x
  have hβ' : β' ≫ ((Over.post B.inclusion).obj V' : Over S).hom = s :=
    congrArg B.inclusion.map (Over.w x)
  have hxβ : x = affineOverHom B S hS hD' s β' hβ' :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)
  have hb' : Space.HasImageIn B S hS (yoneda.obj V')
      (Space.pointsMap B S hS (yoneda.obj V') (yoneda.map f) ⁻¹' Z) T'
      (affineOverHom B S hS hD' s β' hβ') := hxβ ▸ hxI
  refine ⟨β', hβ', hb', congrArg (BigFppfOver.toScheme B S hS).map hix, ?_⟩
  -- uniqueness of lifts along `ψ`
  have hG'w : G'.hom.app (op T') wτ = z :=
    eq_of_comp_eq_of_formallyEtale B S hS _ g ψ G' hw hψf i hi
      (by rw [← NatTrans.naturality_apply G'.hom i.op wτ, hwτ1, hz]) (by rw [hwτ2]; exact h2)
  have hsec : presheafSection B S hS _ hb' = presheafSection B S hS x hxI := by congr 1
  exact (congrArg (G'.hom.app (op T')) (hsec.trans hwx.symm)).trans hG'w

end AlgebraicGeometry.FormalSpace
