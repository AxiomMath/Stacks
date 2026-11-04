module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RepresentedModuleLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Morphisms of modules along a limit of algebraic spaces with compatible charts

Let `A` be an algebraic space, `p_j : Y_j ⟶ A` algebraic spaces over `A` indexed by a cofiltered
category, and `Y` an algebraic space over `A` with morphisms `π_j : Y ⟶ Y_j` over `A`. Suppose
given surjective étale charts `u_j : h_{U_j} ⟶ Y_j` and `h_U ⟶ Y`, where `U_j` is a system of
affine schemes with affine transition morphisms and limit `U`, compatible with the `π_j` and with
the transition morphisms of `U_j` over `A`, and a system `R_j` of quasi-compact schemes with
affine transition morphisms and limit `R` together with morphisms `s_j, t_j : R_j ⟶ U_j`
forming a kernel pair of `u_j`. Then a morphism between the inverse images to `Y` of two
quasi-coherent modules of finite presentation on `A` is, for some `j`, the inverse image of a
morphism between their inverse images to `Y_j`.

## Main results

* `AlgebraicGeometry.Space.exists_modulePullback_map_eq_of_isLimit_pt`,
  `AlgebraicGeometry.Space.exists_descendsAlong_modulePullback_of_isLimit_pt`: Stacks 01ZR (3)
  and (2) on represented systems, with the cone point spelled as such.
* `AlgebraicGeometry.Space.exists_homTransport_eq_of_charts`: the fullness statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stacks 01ZR on represented systems, with the cone point spelled as such -/

section Represented

variable {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ BigFppfOver B S hS) (d : Cone E)

/-- `AlgebraicGeometry.Space.exists_modulePullback_map_eq_of_isLimit` with the projections of the
cone read as morphisms out of the cone point. -/
theorem exists_modulePullback_map_eq_of_isLimit_pt
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    (hd : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d)) (i : J)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj i))]
    {G H : Modules.{u, u} B S hS (schemeSpace (E.obj i)).1 (schemeSpace (E.obj i)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite) (ψ₁ ψ₂ : G ⟶ H)
    (h : (modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app i))).map ψ₁ =
      (modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app i))).map ψ₂) :
    ∃ (j : J) (e : j ⟶ i), (modulePullback B S hS (schemeSpaceMap (E.map e))).map ψ₁ =
      (modulePullback B S hS (schemeSpaceMap (E.map e))).map ψ₂ :=
  exists_modulePullback_map_eq_of_isLimit B S hS E d hd i hG hGfp hH hHfp ψ₁ ψ₂
    (by dsimp only [Functor.const_obj_obj]; exact h)

/-- `AlgebraicGeometry.Space.exists_modulePullback_iso_of_isLimit` with the projections of the
cone read as morphisms out of the cone point. -/
theorem exists_modulePullback_iso_of_isLimit_pt
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    [∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (E.obj j))]
    [∀ j, QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (E.obj j))]
    (hd : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d))
    (G : Modules.{u, u} B S hS (schemeSpace d.pt).1 (schemeSpace d.pt).2)
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite) :
    ∃ (i : J) (Gᵢ : Modules.{u, u} B S hS (schemeSpace (E.obj i)).1 (schemeSpace (E.obj i)).2),
      Gᵢ.IsQuasicoherentOnSite ∧ Gᵢ.IsFinitePresentationOnSite ∧
        Nonempty ((modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app i))).obj Gᵢ ≅ G) := by
  have := exists_modulePullback_iso_of_isLimit B S hS E d hd G hG hGfp
  dsimp only [Functor.const_obj_obj] at this
  exact this

/-- `AlgebraicGeometry.Space.exists_descendsAlong_modulePullback_of_isLimit'` with the
projections of the cone read as morphisms out of the cone point. -/
theorem exists_descendsAlong_modulePullback_of_isLimit_pt
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    (hd : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d)) (i : J)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj d.pt)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))]
    {G H : Modules.{u, u} B S hS (schemeSpace (E.obj i)).1 (schemeSpace (E.obj i)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app i))).obj G ⟶
      (modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app i))).obj H) :
    ∃ (j : J) (e : j ⟶ i),
      ∀ κ : modulePullback B S hS (schemeSpaceMap (E.map e)) ⋙
          modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app j)) ≅
          modulePullback B S hS (schemeSpaceMap (U := d.pt) (d.π.app i)),
        Functor.DescendsAlong κ φ := by
  have := exists_descendsAlong_modulePullback_of_isLimit' B S hS E d hd i hG hGfp hH hHfp
    (by dsimp only [Functor.const_obj_obj]; exact φ)
  dsimp only [Functor.const_obj_obj] at this
  exact this

omit [IsCofiltered J] in
/-- The projections of a cone of schemes, read as morphisms of algebraic spaces, are compatible
with the transition morphisms. -/
theorem schemeSpaceMap_cone_π_comp {i j : J} (f : i ⟶ j) :
    schemeSpaceMap (U := d.pt) (d.π.app i) ≫ schemeSpaceMap (E.map f) =
      schemeSpaceMap (U := d.pt) (d.π.app j) :=
  ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (d.w f)))

end Represented

/-! ### Fullness along a limit with compatible charts -/

/-- Iterated inverse images of a morphism along two factorizations of the same morphism agree. -/
private theorem homTransport_homTransport_eq_of_comp_eq {A : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} {P T T₁ T₂ : AlgebraicSpaces B S hS} {a : T ⟶ T₁}
    {b : T₁ ⟶ P} {c : T ⟶ T₂} {d : T₂ ⟶ P} (h : a ≫ b = c ≫ d) {p : P ⟶ A} {v₁ : T₁ ⟶ A}
    {v₂ : T₂ ⟶ A} {v : T ⟶ A} (hb : b ≫ p = v₁) (hd : d ≫ p = v₂) (ha : a ≫ v₁ = v)
    (hc : c ≫ v₂ = v) (ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    homTransport M N a ha (homTransport M N b hb ψ) =
      homTransport M N c hc (homTransport M N d hd ψ) := by
  have h₁ : (a ≫ b) ≫ p = v := by rw [Category.assoc, hb, ha]
  have h₂ : (c ≫ d) ≫ p = v := by rw [Category.assoc, hd, hc]
  rw [homTransport_homTransport _ _ _ _ h₁, homTransport_congr h _ h₂,
    ← homTransport_homTransport _ _ hd hc h₂]

/-- **A morphism of inverse images to the limit descends to a stage**, for a system of algebraic
spaces `Y_j` over `A` with affine étale surjective charts `h_{U_j} ⟶ Y_j` forming a system of
affine schemes with limit a chart of the limit `Y`, and with kernel pairs `R_j` forming a system
of quasi-compact schemes. -/
theorem exists_homTransport_eq_of_charts {A : AlgebraicSpaces B S hS}
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    {Y : J → AlgebraicSpaces B S hS} (p : ∀ j, Y j ⟶ A)
    {Yc : AlgebraicSpaces B S hS} {pc : Yc ⟶ A} (π : ∀ j, Yc ⟶ Y j) (hπ : ∀ j, π j ≫ p j = pc)
    {E : J ⥤ BigFppfOver B S hS} (d : Cone E)
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map e))]
    [∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj j))]
    (hd : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d))
    (u : ∀ j, schemeSpace (E.obj j) ⟶ Y j) (uc : schemeSpace d.pt ⟶ Yc)
    (hu : ∀ {j j' : J} (f : j ⟶ j'), schemeSpaceMap (E.map f) ≫ u j' ≫ p j' = u j ≫ p j)
    (hdu : ∀ j, uc ≫ π j = schemeSpaceMap (U := d.pt) (d.π.app j) ≫ u j)
    (hue : ∀ j, IsEtale B S hS (u j).hom)
    (hucov : ∀ j, IsEtaleCovering B S hS (fun _ : Unit => (schemeSpace (E.obj j)).1)
      (fun _ => (u j).hom))
    (huc : IsEtaleCovering B S hS (fun _ : Unit => (schemeSpace d.pt).1) (fun _ => uc.hom))
    {F : J ⥤ BigFppfOver B S hS} (d' : Cone F)
    [∀ {i j : J} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (F.map e))]
    [∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj (F.obj j))]
    (hd' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d'))
    (s t : ∀ j, schemeSpace (F.obj j) ⟶ schemeSpace (E.obj j))
    (sc tc : schemeSpace d'.pt ⟶ schemeSpace d.pt)
    (hs : ∀ {j j' : J} (f : j ⟶ j'),
      schemeSpaceMap (F.map f) ≫ s j' = s j ≫ schemeSpaceMap (E.map f))
    (ht : ∀ {j j' : J} (f : j ⟶ j'),
      schemeSpaceMap (F.map f) ≫ t j' = t j ≫ schemeSpaceMap (E.map f))
    (hsc : ∀ j, schemeSpaceMap (U := d'.pt) (d'.π.app j) ≫ s j =
      sc ≫ schemeSpaceMap (U := d.pt) (d.π.app j))
    (htc : ∀ j, schemeSpaceMap (U := d'.pt) (d'.π.app j) ≫ t j =
      tc ≫ schemeSpaceMap (U := d.pt) (d.π.app j))
    (hstc : sc ≫ uc = tc ≫ uc)
    (hk : ∀ j, IsPullback (s j).hom (t j).hom (u j).hom (u j).hom)
    {G H : Modules.{u, u} B S hS A.1 A.2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS pc).obj G ⟶ (modulePullback B S hS pc).obj H) :
    ∃ (j : J) (χ : (modulePullback B S hS (p j)).obj G ⟶ (modulePullback B S hS (p j)).obj H),
      homTransport G H (π j) (hπ j) χ = φ := by
  have : ∀ i, IsAffine ((E ⋙ BigFppfOver.toScheme B S hS).obj i) := fun i =>
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.pt) :=
    Scheme.isAffine_of_isLimit (D := E ⋙ BigFppfOver.toScheme B S hS) _ hd
  obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
  have e₂ : ∀ j, schemeSpaceMap (U := d.pt) (d.π.app j) ≫ u j ≫ p j = uc ≫ pc := fun j => by
    rw [← Category.assoc, ← hdu, Category.assoc, hπ]
  have hsu : ∀ j, s j ≫ u j = t j ≫ u j := fun j => ObjectProperty.hom_ext _ (hk j).w
  have hts : ∀ j, t j ≫ u j ≫ p j = s j ≫ u j ≫ p j := fun j => by
    rw [← Category.assoc, ← hsu, Category.assoc]
  have hrs : ∀ j, schemeSpaceMap (U := d'.pt) (d'.π.app j) ≫ s j ≫ u j ≫ p j =
      sc ≫ uc ≫ pc := fun j => by
    rw [← Category.assoc, hsc, Category.assoc, e₂]
  have hrF : ∀ {j j' : J} (f : j ⟶ j'),
      schemeSpaceMap (F.map f) ≫ s j' ≫ u j' ≫ p j' = s j ≫ u j ≫ p j := fun f => by
    rw [← Category.assoc, hs f, Category.assoc, hu f]
  let φU := homTransport G H uc rfl φ
  let φ' := (pullbackComparison B S hS (schemeSpaceMap (U := d.pt) (d.π.app j₀))
      (u j₀ ≫ p j₀) _ (e₂ j₀) G).inv ≫ φU ≫
    (pullbackComparison B S hS (schemeSpaceMap (U := d.pt) (d.π.app j₀))
      (u j₀ ≫ p j₀) _ (e₂ j₀) H).hom
  have hφ' : homRebase G H _ (e₂ j₀) φ' = φU := by
    rw [homRebase_def]
    simp only [φ', Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  obtain ⟨k, f, hdesc⟩ := exists_descendsAlong_modulePullback_of_isLimit_pt E d hd j₀
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG)
    (isFinitePresentationOnSite_modulePullback B S hS _ G hGfp)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ H hH)
    (isFinitePresentationOnSite_modulePullback B S hS _ H hHfp) φ'
  obtain ⟨ψ', hψ'⟩ := (descendsAlong_pullbackComparisonNatIso_iff _ _ _
    (schemeSpaceMap_cone_π_comp E d f) φ').mp (hdesc _)
  let ψU := homRebase G H (schemeSpaceMap (E.map f)) (hu f) ψ'
  have hψU : homTransport G H (schemeSpaceMap (U := d.pt) (d.π.app k)) (e₂ k) ψU = φU := by
    rw [homTransport_homRebase _ _ _ _ (schemeSpaceMap_cone_π_comp E d f) (e₂ j₀), hψ', hφ']
  have key : ∀ (g : schemeSpace (F.obj k) ⟶ schemeSpace (E.obj k))
      (gc : schemeSpace d'.pt ⟶ schemeSpace d.pt)
      (hgc : schemeSpaceMap (U := d'.pt) (d'.π.app k) ≫ g =
        gc ≫ schemeSpaceMap (U := d.pt) (d.π.app k))
      {r : schemeSpace (F.obj k) ⟶ A} (hg : g ≫ u k ≫ p k = r) {rc : schemeSpace d'.pt ⟶ A}
      (hr : schemeSpaceMap (U := d'.pt) (d'.π.app k) ≫ r = rc) (hrc : (gc ≫ uc) ≫ pc = rc),
      homTransport G H (schemeSpaceMap (U := d'.pt) (d'.π.app k)) hr
          (homTransport G H g hg ψU) = homTransport G H (gc ≫ uc) hrc φ := by
    intro g gc hgc r hg rc hr hrc
    have h₃ : gc ≫ uc ≫ pc = rc := by rw [← Category.assoc, hrc]
    rw [homTransport_homTransport_eq_of_comp_eq hgc hg (e₂ k) hr h₃, hψU,
      homTransport_homTransport _ _ _ _ hrc]
  have hR : (modulePullback B S hS (schemeSpaceMap (U := d'.pt) (d'.π.app k))).map
        (homTransport G H (s k) rfl ψU) =
      (modulePullback B S hS (schemeSpaceMap (U := d'.pt) (d'.π.app k))).map
        (homTransport G H (t k) (hts k) ψU) := by
    apply homRebase_injective _ (hrs k)
    rw [← homTransport_def, ← homTransport_def,
      key (s k) sc (hsc k) rfl (hrs k) (Category.assoc _ _ _),
      key (t k) tc (htc k) (hts k) (hrs k) (by rw [← hstc, Category.assoc]),
      homTransport_congr hstc]
  obtain ⟨k', f', hk'⟩ := exists_modulePullback_map_eq_of_isLimit_pt F d' hd' k
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG)
    (isFinitePresentationOnSite_modulePullback B S hS _ G hGfp)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ H hH)
    (isFinitePresentationOnSite_modulePullback B S hS _ H hHfp) _ _ hR
  let ψ'' := homTransport G H (schemeSpaceMap (E.map f')) (hu f') ψU
  have hkp : ∀ (g : schemeSpace (F.obj k') ⟶ schemeSpace (E.obj k'))
      (g₀ : schemeSpace (F.obj k) ⟶ schemeSpace (E.obj k))
      (hgg : schemeSpaceMap (F.map f') ≫ g₀ = g ≫ schemeSpaceMap (E.map f'))
      {r₀ : schemeSpace (F.obj k) ⟶ A} (hg₀ : g₀ ≫ u k ≫ p k = r₀)
      {r : schemeSpace (F.obj k') ⟶ A} (hg : g ≫ u k' ≫ p k' = r)
      (hr : schemeSpaceMap (F.map f') ≫ r₀ = r),
      homTransport G H g hg ψ'' =
        homTransport G H (schemeSpaceMap (F.map f')) hr (homTransport G H g₀ hg₀ ψU) := by
    intro g g₀ hgg r₀ hg₀ r hg hr
    exact homTransport_homTransport_eq_of_comp_eq hgg.symm (hu f') hg₀ hg hr _
  have hst : homTransport G H (s k') rfl ψ'' = homTransport G H (t k') (hts k') ψ'' := by
    rw [hkp (s k') (s k) (hs f') rfl rfl (hrF f'), hkp (t k') (t k) (ht f') (hts k) (hts k')
        (hrF f'), homTransport_def (schemeSpaceMap (F.map f')),
      homTransport_def (schemeSpaceMap (F.map f')), hk']
  have hψ'' : homTransport G H (schemeSpaceMap (U := d.pt) (d.π.app k')) (e₂ k') ψ'' = φU := by
    have h₁ : (schemeSpaceMap (U := d.pt) (d.π.app k') ≫ schemeSpaceMap (E.map f')) ≫
        u k ≫ p k = uc ≫ pc := by
      rw [schemeSpaceMap_cone_π_comp, e₂]
    rw [homTransport_homTransport _ _ _ _ h₁,
      homTransport_congr (schemeSpaceMap_cone_π_comp E d f') _ (e₂ k), hψU]
  obtain ⟨χ, hχ⟩ := exists_homTransport_eq_of_isPullback (u k') (hue k')
    (relativelyRepresentable_of_isAlgebraicSpace B S hS (Y k').2 _) (hucov k') (hk k') (p k')
    rfl ψ'' rfl (hts k') hst
  refine ⟨k', χ, homTransport_injective uc huc rfl ?_⟩
  rw [homTransport_homTransport_eq_of_comp_eq (hdu k') (hπ k') rfl rfl (e₂ k'), hχ, hψ'']

end AlgebraicGeometry.Space

end
