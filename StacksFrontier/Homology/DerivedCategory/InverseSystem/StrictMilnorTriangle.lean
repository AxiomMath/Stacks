module

public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorAmplitude
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact
public import StacksFrontier.Homology.DerivedComplete.DerivedLimitPinning
public import StacksFrontier.Homology.DerivedComplete.MilnorEpiTower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A strict Milnor triangle: the pinned two-out-of-three along a short exact sequence of towers

`CategoryTheory.Pretriangulated.IsDerivedLimit` is a property of an object, so it says nothing
about which maps to the terms of the tower the limit carries; the predicate that does is
`NoetherianAdicCompletion.IsDerivedLimitWithProjections`. This file supplies derived limits with
*named* projections for towers that are strictified — towers of honest cochain complexes — and the
distinguished triangle that three such towers in a short exact sequence produce, again with named
maps compatible with the projections on the nose.

## Main results

* `NoetherianAdicCompletion.isDerivedLimitWithProjections_of_isLimit_fan` — the pinned transport:
  a distinguished triangle `X ⟶ P ⟶ P ⟶ X⟦1⟧` whose second vertex is the vertex of a limit fan
  over the tower, and whose middle map is the difference map in the fan's coordinates, exhibits
  `X` as a derived limit *with the projections of the fan composed with the first map*. This is
  the pinned form of `DerivedCategory.isDerivedLimit_of_fan`.
* `DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi` — **the functorial `Rlim`.** For
  a tower of cochain complexes of modules with epimorphic transition maps, the image under `Q` of
  the *ordinary* limit is a derived limit of the tower in `D(ModuleCat A)`, with projections the
  images under `Q` of the limit projections. Nothing is chosen: both the object and the
  projections are computed from the tower. This is the pinned form of
  `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi`.
* `DerivedCategory.isIso_limitLift_homology_Q_limit_of_epi` — in a degree `r` in which the terms
  have no cohomology in degree `r - 1`, the map `Hʳ(Q(lim F)) ⟶ lim Hʳ(Q Fₙ)` induced by the
  limit projections is an isomorphism: the Milnor sequence with its `R¹lim` term zero.
* `DerivedCategory.shortExact_map_lim_of_surjective` — the ordinary limit of a short exact
  sequence of towers of complexes with degreewise surjective transition maps on the sub-tower is
  short exact.
* `DerivedCategory.isDerivedLimitWithProjections_triangle_of_shortExact` — **the pinned
  two-out-of-three.** All three ordinary limits are derived limits with their own projections, and
  the two limit maps sit in a distinguished triangle whose maps are compatible with those
  projections levelwise.

## Implementation notes

The obstruction that makes this file necessary is that the nine lemma
(`CategoryTheory.Triangulated.exists_nine_diagram`) cannot produce the third column pinned. Given
Milnor triangles for the first two towers `F ⟶ G` and a distinguished row of products, its
conclusion clause `v₁ ≫ b₂ = a₂ ≫ w₁` forces the comparison `w₁` to be the product of the
level maps only up to a morphism factoring through the connecting map, that is, up to
`Hom(K_F⟦1⟧, ∏ₙ Gₙ)`, which does not vanish. Strictifying removes the obstruction because every
map in sight is then the image under `Q` of a map of complexes, and the compatibilities hold
already at the complex level, where `Pi.lift` and `limMap` are honest functions.

The right-exactness of the ordinary limit is the one non-formal input; it is
`Stacks.Algebraization.shortExact_map_lim_of_isMittagLeffler` (Tag 03CA), applied degreewise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace NoetherianAdicCompletion

/-- **The pinned transport of a derived limit along a limit fan.** A distinguished triangle
`X ⟶ P ⟶ P ⟶ X⟦1⟧` whose second vertex is the vertex of a limit fan `π` over
`fun n : ℕ ↦ F.obj ⟨n⟩`, and whose middle map is the difference map in the coordinates of that
fan, exhibits `X` as a derived limit of `F` **with projections** `p ≫ π n`.

This is `DerivedCategory.isDerivedLimit_of_fan` with the projections retained: the comparison
`P ≅ ∏ᶜ Fₙ` carries `π n` to the categorical projection, so the first map of the transported
triangle is the product of the maps `p ≫ π n` and not merely some map into the product. -/
public theorem isDerivedLimitWithProjections_of_isLimit_fan
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) {P X : D} (π : ∀ n : ℕ, P ⟶ F.obj ⟨n⟩)
    (hπ : IsLimit (Fan.mk P π)) (p : X ⟶ P) (d : P ⟶ P) (δ : P ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p d δ ∈ distTriang D)
    (hd : ∀ n : ℕ, d ≫ π n = π n - π (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
    (ρ : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩) (hρ : ∀ n : ℕ, p ≫ π n = ρ n) :
    ∃ _ : HasProduct (fun n : ℕ ↦ F.obj ⟨n⟩), IsDerivedLimitWithProjections F X ρ := by
  have hP : HasProduct (fun n : ℕ ↦ F.obj ⟨n⟩) := ⟨⟨_, hπ⟩⟩
  refine ⟨hP, ?_⟩
  let eP : P ≅ ∏ᶜ (fun n : ℕ ↦ F.obj ⟨n⟩) := hπ.conePointUniqueUpToIso (limit.isLimit _)
  have heP : ∀ n : ℕ, eP.hom ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n = π n := fun n ↦
    hπ.conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨n⟩
  have hlift : Pi.lift ρ = p ≫ eP.hom := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Pi.lift_π, Category.assoc, heP, hρ]
  have hcomm : d ≫ eP.hom = eP.hom ≫ Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, heP, hd n, Category.assoc, Pi.lift_π, Preadditive.comp_sub,
      heP, ← Category.assoc, heP]
  refine ⟨eP.inv ≫ δ, isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl X) eP.symm eP.symm ?_ ?_ ?_
  · dsimp
    rw [hlift, Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · dsimp
    rw [← cancel_epi eP.hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← hcomm, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · dsimp
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end NoetherianAdicCompletion

namespace DerivedCategory

/-- **The functorial `Rlim` of a strictified tower, with pinned projections.** For a tower of
cochain complexes of `A`-modules whose transition maps are epimorphisms, the image under `Q` of
the *ordinary* inverse limit is a derived limit of the tower in `D(A)`, and its projections are
the images under `Q` of the projections of the ordinary limit.

This is `DerivedCategory.isDerivedLimit_of_limit_cone_of_epi` with the projections retained.
Nothing here is chosen: the object is `limit F` and the projections are `limit.π F ⟨n⟩`, both
functorial in `F`, which is what makes the maps of
`DerivedCategory.isDerivedLimitWithProjections_triangle_of_shortExact` compatible with the
projections on the nose. -/
public theorem isDerivedLimitWithProjections_Q_limit_of_epi
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ)
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)] :
    ∃ _ : HasProduct (fun n : ℕ ↦ (F ⋙ DerivedCategory.Q).obj ⟨n⟩),
      NoetherianAdicCompletion.IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (limit F)) (fun n : ℕ ↦ DerivedCategory.Q.map (limit.π F ⟨n⟩)) := by
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q (C := ModuleCat.{v} A)) := Stacks.DerivedProducts.preservesLimitsOfShape_Q
  -- The complex-level Milnor sequence `0 ⟶ limit F ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ 0`.
  let k := inverseSystemLimitKernelFork F
  have hk := inverseSystemLimitKernelForkIsLimit F
  have : Epi (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) := by
    -- Degreewise: evaluation in a degree preserves the product, and there the difference map
    -- of an epimorphic tower of modules is an epimorphism.
    apply HomologicalComplex.epi_of_epi_f
    intro i
    let G := HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) i
    let X := fun n : ℕ ↦ F.obj ⟨n⟩
    let t := fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op
    have : ∀ n, Epi (G.map (t n)) := fun n ↦ inferInstance
    have hd := CountableMilnorTower.epi_pi_sub_shift_of_epi (fun n ↦ G.obj (X n))
      (fun n ↦ G.map (t n))
    let d := Pi.lift fun n ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n
    let d' := Pi.lift fun n ↦ Pi.π (fun n ↦ G.obj (X n)) n -
      Pi.π (fun n ↦ G.obj (X n)) (n + 1) ≫ G.map (t n)
    let e := asIso (piComparison G X)
    have he : G.map d ≫ e.hom = e.hom ≫ d' := by
      apply Pi.hom_ext
      intro n
      change (G.map d ≫ piComparison G X) ≫ Pi.π _ n = (piComparison G X ≫ d') ≫ Pi.π _ n
      rw [Category.assoc, piComparison_comp_π, ← G.map_comp]
      simp only [d, d', Pi.lift_π, G.map_sub, G.map_comp, Category.assoc,
        Preadditive.comp_sub, piComparison_comp_π_assoc, piComparison_comp_π]
    have : Epi (G.map d ≫ e.hom) := by
      rw [he]
      infer_instance
    exact (epi_comp_iff_of_isIso _ e.hom).1 this
  let S := ShortComplex.mk k.ι _ k.condition
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S hk
      mono_f := mono_of_isLimit_fork hk
      epi_g := inferInstance }
  -- Transport its triangle along the product fan in the derived category.
  refine NoetherianAdicCompletion.isDerivedLimitWithProjections_of_isLimit_fan
    (F ⋙ DerivedCategory.Q) (fun n : ℕ ↦ DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n))
    (Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory
      (fun n : ℕ ↦ F.obj ⟨n⟩)))
    (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g) (DerivedCategory.triangleOfSESδ hS)
    (DerivedCategory.triangleOfSES_distinguished hS) (fun n ↦ ?_) _ (fun n ↦ ?_)
  · rw [← DerivedCategory.Q.map_comp]
    change DerivedCategory.Q.map ((Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n - Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op) ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) = _
    rw [Pi.lift_π, DerivedCategory.Q.map_sub, DerivedCategory.Q.map_comp]
    rfl
  · rw [← DerivedCategory.Q.map_comp]
    change DerivedCategory.Q.map ((Pi.lift fun n : ℕ ↦ limit.π F ⟨n⟩) ≫
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) = _
    rw [Pi.lift_π]

/-! ### The limit of a short exact sequence of towers of complexes -/

/-- **The ordinary limit of a short exact sequence of towers of complexes is short exact**, as
soon as the transition maps of the sub-tower are degreewise surjective.

Left exactness is automatic; the content is the surjectivity of `lim S.X₂ ⟶ lim S.X₃`, which is
the Mittag-Leffler vanishing `R¹lim S.X₁ = 0`. The proof is degreewise: limits of complexes and
short exactness of complexes are both computed in each degree, and in a fixed degree this is
`CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler`, Tag 03CA. -/
@[ega "0 13.2.2" "special case", ega "III 4.1.7.21" "more general"]
public theorem shortExact_map_lim_of_surjective
    {A : Type u} [CommRing A]
    (S : ShortComplex (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj n)).ShortExact)
    (hsurj : ∀ (n : ℕ) (q : ℤ),
      Function.Surjective ((S.X₁.map (homOfLE (Nat.le_succ n)).op).f q)) :
    (S.map (lim : (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) ⥤
      CochainComplex (ModuleCat.{v} A) ℤ)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro q
  let E := HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) q
  rw [← ShortComplex.map_comp,
    ShortComplex.shortExact_iff_of_iso (S.mapNatIso (preservesLimitNatIso (J := ℕᵒᵖ) E)),
    ShortComplex.map_comp]
  refine CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler _ (fun n ↦ ?_) ?_
  · rw [← ShortComplex.map_comp]
    exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (hS n) q
  · exact Stacks.DerivedLimit.isMittagLeffler_of_eventually_surjective 0 fun n _ ↦ hsurj n q

/-- Epimorphic transition maps for a tower of complexes of modules, from degreewise
surjectivity. -/
public theorem epi_map_of_surjective {A : Type u} [CommRing A]
    {F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ}
    (h : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((F.map (homOfLE (Nat.le_succ n)).op).f q))
    (n : ℕ) : Epi (F.map (homOfLE (Nat.le_succ n)).op) :=
  HomologicalComplex.epi_of_epi_f _ fun q ↦ (ModuleCat.epi_iff_surjective _).2 (h n q)

/-! ### The pinned Milnor triangle -/

/-- **The limit comparison of a map of towers of complexes is compatible with the limit
projections**, in the derived category. This is the clause that makes the triangle of
`DerivedCategory.isDerivedLimitWithProjections_triangle_of_shortExact` *pinned*: it holds already
at the complex level, where `limMap` is characterized by it. -/
public theorem Q_map_limMap_comp_Q_map_limit_π {A : Type u} [CommRing A]
    {F G : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (φ : F ⟶ G) (n : ℕ) :
    DerivedCategory.Q.map (limMap φ) ≫ DerivedCategory.Q.map (limit.π G ⟨n⟩) =
      DerivedCategory.Q.map (limit.π F ⟨n⟩) ≫ DerivedCategory.Q.map (φ.app ⟨n⟩) := by
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, limMap_π]

/-- A comparison iso compatible with the limit projections of `F` is compatible with those of `G`
after composing with the image of `limMap φ`. -/
private theorem iso_hom_comp_Q_map_limMap_comp_Q_map_limit_π {A : Type u} [CommRing A]
    {F G : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (φ : F ⟶ G)
    {K : DerivedCategory (ModuleCat.{v} A)} (e : K ≅ DerivedCategory.Q.obj (limit F))
    (π : ∀ n : ℕ, K ⟶ (F ⋙ DerivedCategory.Q).obj ⟨n⟩)
    (he : ∀ n : ℕ, e.hom ≫ DerivedCategory.Q.map (limit.π F ⟨n⟩) = π n) (n : ℕ) :
    e.hom ≫ DerivedCategory.Q.map (limMap φ) ≫ DerivedCategory.Q.map (limit.π G ⟨n⟩) =
      π n ≫ DerivedCategory.Q.map (φ.app ⟨n⟩) := by
  rw [Q_map_limMap_comp_Q_map_limit_π, ← Category.assoc, he]

/-- **The pinned two-out-of-three, strict form.** Let `0 ⟶ T₁ ⟶ T₂ ⟶ T₃ ⟶ 0` be a short exact
sequence of towers of cochain complexes of `A`-modules, short exact at every level, with
degreewise surjective transition maps. Then:

* each of the three ordinary inverse limits is, through `Q`, a derived limit of its tower **with
  the projections of the ordinary limit** — `isDerivedLimitWithProjections_Q_limit_of_epi`;
* the two limit comparison maps sit in a distinguished triangle of `D(A)`;
* and those maps are compatible with the three families of projections on the nose —
  `Q_map_limMap_comp_Q_map_limit_π`.

This is the statement the nine lemma cannot supply. Given Milnor triangles for the first two
towers and a distinguished row of products, the conclusion clause `v₁ ≫ b₂ = a₂ ≫ w₁` of
`CategoryTheory.Triangulated.exists_nine_diagram` determines the third column's comparison only
up to a morphism factoring through the connecting map of the first Milnor triangle, that is up to
`Hom(Rlim T₁⟦1⟧, ∏ₙ (T₂)ₙ)`, which is not zero. Here every map is the image under `Q` of a map of
complexes and the compatibilities are complex-level identities, so nothing is left unpinned. -/
public theorem isDerivedLimitWithProjections_triangle_of_shortExact
    {A : Type u} [CommRing A]
    (S : ShortComplex (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj n)).ShortExact)
    (h₁ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₁.map (homOfLE (Nat.le_succ n)).op).f q))
    (h₂ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₂.map (homOfLE (Nat.le_succ n)).op).f q))
    (h₃ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₃.map (homOfLE (Nat.le_succ n)).op).f q)) :
    ∃ (_ : HasProduct fun n : ℕ ↦ (S.X₁ ⋙ DerivedCategory.Q).obj ⟨n⟩)
      (_ : HasProduct fun n : ℕ ↦ (S.X₂ ⋙ DerivedCategory.Q).obj ⟨n⟩)
      (_ : HasProduct fun n : ℕ ↦ (S.X₃ ⋙ DerivedCategory.Q).obj ⟨n⟩),
      NoetherianAdicCompletion.IsDerivedLimitWithProjections (S.X₁ ⋙ DerivedCategory.Q)
          (DerivedCategory.Q.obj (limit S.X₁))
          (fun n : ℕ ↦ DerivedCategory.Q.map (limit.π S.X₁ ⟨n⟩)) ∧
        NoetherianAdicCompletion.IsDerivedLimitWithProjections (S.X₂ ⋙ DerivedCategory.Q)
          (DerivedCategory.Q.obj (limit S.X₂))
          (fun n : ℕ ↦ DerivedCategory.Q.map (limit.π S.X₂ ⟨n⟩)) ∧
        NoetherianAdicCompletion.IsDerivedLimitWithProjections (S.X₃ ⋙ DerivedCategory.Q)
          (DerivedCategory.Q.obj (limit S.X₃))
          (fun n : ℕ ↦ DerivedCategory.Q.map (limit.π S.X₃ ⟨n⟩)) ∧
        ∃ δ : DerivedCategory.Q.obj (limit S.X₃) ⟶
            (DerivedCategory.Q.obj (limit S.X₁))⟦(1 : ℤ)⟧,
          Triangle.mk (DerivedCategory.Q.map (limMap S.f))
              (DerivedCategory.Q.map (limMap S.g)) δ ∈
            distTriang (DerivedCategory (ModuleCat.{v} A)) := by
  have : ∀ n : ℕ, Epi (S.X₁.map (homOfLE (Nat.le_succ n)).op) := epi_map_of_surjective h₁
  have : ∀ n : ℕ, Epi (S.X₂.map (homOfLE (Nat.le_succ n)).op) := epi_map_of_surjective h₂
  have : ∀ n : ℕ, Epi (S.X₃.map (homOfLE (Nat.le_succ n)).op) := epi_map_of_surjective h₃
  obtain ⟨p₁, hp₁⟩ := isDerivedLimitWithProjections_Q_limit_of_epi S.X₁
  obtain ⟨p₂, hp₂⟩ := isDerivedLimitWithProjections_Q_limit_of_epi S.X₂
  obtain ⟨p₃, hp₃⟩ := isDerivedLimitWithProjections_Q_limit_of_epi S.X₃
  refine ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃,
    DerivedCategory.triangleOfSESδ (shortExact_map_lim_of_surjective S hS h₁),
    DerivedCategory.triangleOfSES_distinguished (shortExact_map_lim_of_surjective S hS h₁)⟩

/-- **The pinned two-out-of-three, transported onto given derived limits.** Let
`0 ⟶ T₁ ⟶ T₂ ⟶ T₃ ⟶ 0` be a short exact sequence of towers of cochain complexes of `A`-modules
as in `DerivedCategory.isDerivedLimitWithProjections_triangle_of_shortExact`, and let `K₁` with
projections `π₁` and `K₂` with projections `π₂` be derived limits of the first two towers —
*anywhere* in `D(A)`, not necessarily the strict ones. Then there are a map `α : K₁ ⟶ K₂`, an
object `K₃` with projections `π₃` which is a derived limit of the third tower, and maps `β`, `γ`
making `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧` distinguished, such that `α` and `β` are compatible with the three
families of projections levelwise.

The maps `α` and `β` are *produced*, not matched against given ones: forcing a given
`α : K₁ ⟶ K₂` compatible with the projections to be the comparison of the strict limits is
exactly the vanishing of `Hom(K₁⟦1⟧, ∏ₙ (T₂)ₙ)`, since two maps `K₁ ⟶ K₂` agreeing after every
projection differ by a map factoring through the connecting morphism of the Milnor triangle of
`K₂`. That group does not vanish in general, which is why a hypothesis supplying the first map of
the triangle cannot be accommodated. -/
public theorem exists_isDerivedLimitWithProjections_triangle_of_shortExact
    {A : Type u} [CommRing A]
    (S : ShortComplex (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj n)).ShortExact)
    (h₁ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₁.map (homOfLE (Nat.le_succ n)).op).f q))
    (h₂ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₂.map (homOfLE (Nat.le_succ n)).op).f q))
    (h₃ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₃.map (homOfLE (Nat.le_succ n)).op).f q))
    [HasProduct fun n : ℕ ↦ (S.X₁ ⋙ DerivedCategory.Q).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (S.X₂ ⋙ DerivedCategory.Q).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (S.X₃ ⋙ DerivedCategory.Q).obj ⟨n⟩]
    {K₁ K₂ : DerivedCategory (ModuleCat.{v} A)}
    {π₁ : ∀ n : ℕ, K₁ ⟶ (S.X₁ ⋙ DerivedCategory.Q).obj ⟨n⟩}
    {π₂ : ∀ n : ℕ, K₂ ⟶ (S.X₂ ⋙ DerivedCategory.Q).obj ⟨n⟩}
    (hK₁ : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (S.X₁ ⋙ DerivedCategory.Q) K₁ π₁)
    (hK₂ : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (S.X₂ ⋙ DerivedCategory.Q) K₂ π₂) :
    ∃ (K₃ : DerivedCategory (ModuleCat.{v} A))
      (π₃ : ∀ n : ℕ, K₃ ⟶ (S.X₃ ⋙ DerivedCategory.Q).obj ⟨n⟩)
      (α : K₁ ⟶ K₂) (β : K₂ ⟶ K₃) (γ : K₃ ⟶ K₁⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{v} A)) ∧
        NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (S.X₃ ⋙ DerivedCategory.Q) K₃ π₃ ∧
        (∀ n : ℕ, α ≫ π₂ n = π₁ n ≫ DerivedCategory.Q.map (S.f.app ⟨n⟩)) ∧
        (∀ n : ℕ, β ≫ π₃ n = π₂ n ≫ DerivedCategory.Q.map (S.g.app ⟨n⟩)) := by
  obtain ⟨p₁, p₂, p₃, hR₁, hR₂, hR₃, δ, hδ⟩ :=
    isDerivedLimitWithProjections_triangle_of_shortExact S hS h₁ h₂ h₃
  obtain ⟨e₁, he₁⟩ := NoetherianAdicCompletion.exists_iso_of_isDerivedLimitWithProjections hK₁ hR₁
  obtain ⟨e₂, he₂⟩ := NoetherianAdicCompletion.exists_iso_of_isDerivedLimitWithProjections hK₂ hR₂
  refine ⟨DerivedCategory.Q.obj (limit S.X₃),
    fun n ↦ DerivedCategory.Q.map (limit.π S.X₃ ⟨n⟩),
    e₁.hom ≫ DerivedCategory.Q.map (limMap S.f) ≫ e₂.inv,
    e₂.hom ≫ DerivedCategory.Q.map (limMap S.g),
    δ ≫ (shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (1 : ℤ)).map e₁.inv, ?_, hR₃,
    fun n ↦ ?_, fun n ↦ ?_⟩
  · exact isomorphic_distinguished _ hδ _
      (Triangle.isoMk _ _ e₁ e₂ (Iso.refl _) (by simp) (by simp) (by simp))
  · rw [Category.assoc, Category.assoc, ← he₂ n, Iso.inv_hom_id_assoc,
      iso_hom_comp_Q_map_limMap_comp_Q_map_limit_π _ e₁ _ he₁]
  · rw [Category.assoc, iso_hom_comp_Q_map_limMap_comp_Q_map_limit_π _ e₂ _ he₂]

/-- **The pinned two-out-of-three along a *given* distinguished triangle.** Let
`0 ⟶ T₁ ⟶ T₂ ⟶ T₃ ⟶ 0` be a short exact sequence of towers of cochain complexes of `A`-modules
as in `DerivedCategory.isDerivedLimitWithProjections_triangle_of_shortExact`, let `K₁` with `π₁`
and `K₂` with `π₂` be derived limits of the first two towers, and let
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧` be a distinguished triangle whose first map is compatible with the
projections. Then `K₃` is a derived limit of the third tower, with projections pinned by the
second map of the triangle — **provided** maps out of `K₁` into `K₂` are separated by the
projections `π₂`.

That separation hypothesis is the whole obstruction, and it is exactly what the nine lemma cannot
discharge: two maps `K₁ ⟶ K₂` agreeing after every `π₂ n` agree after `Pi.lift π₂`, hence differ
by a map factoring through the shifted connecting morphism of the Milnor triangle of `K₂`, so the
hypothesis is the vanishing of the image of `Hom(K₁⟦1⟧, ∏ₙ (T₂)ₙ) ⟶ Hom(K₁, K₂)`. Without it the
given `α` need not be the comparison of the strict limits, and the triangle cannot be compared
with the strict one. With strictification in hand this is the *only* thing left: everything else
in the comparison is a complex-level identity.

When no such hypothesis is available, use
`DerivedCategory.exists_isDerivedLimitWithProjections_triangle_of_shortExact`, which produces its
own first map instead of accepting one. -/
public theorem isDerivedLimitWithProjections_of_distTriang_of_separated
    {A : Type u} [CommRing A]
    (S : ShortComplex (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj n)).ShortExact)
    (h₁ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₁.map (homOfLE (Nat.le_succ n)).op).f q))
    (h₂ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₂.map (homOfLE (Nat.le_succ n)).op).f q))
    (h₃ : ∀ (n : ℕ) (q : ℤ), Function.Surjective ((S.X₃.map (homOfLE (Nat.le_succ n)).op).f q))
    [HasProduct fun n : ℕ ↦ (S.X₁ ⋙ DerivedCategory.Q).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (S.X₂ ⋙ DerivedCategory.Q).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (S.X₃ ⋙ DerivedCategory.Q).obj ⟨n⟩]
    {K₁ K₂ K₃ : DerivedCategory (ModuleCat.{v} A)}
    {π₁ : ∀ n : ℕ, K₁ ⟶ (S.X₁ ⋙ DerivedCategory.Q).obj ⟨n⟩}
    {π₂ : ∀ n : ℕ, K₂ ⟶ (S.X₂ ⋙ DerivedCategory.Q).obj ⟨n⟩}
    (hK₁ : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (S.X₁ ⋙ DerivedCategory.Q) K₁ π₁)
    (hK₂ : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (S.X₂ ⋙ DerivedCategory.Q) K₂ π₂)
    {α : K₁ ⟶ K₂} {β : K₂ ⟶ K₃} {γ : K₃ ⟶ K₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{v} A)))
    (hα : ∀ n : ℕ, α ≫ π₂ n = π₁ n ≫ DerivedCategory.Q.map (S.f.app ⟨n⟩))
    (hsep : ∀ θ : K₁ ⟶ K₂, (∀ n : ℕ, θ ≫ π₂ n = 0) → θ = 0) :
    ∃ π₃ : ∀ n : ℕ, K₃ ⟶ (S.X₃ ⋙ DerivedCategory.Q).obj ⟨n⟩,
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (S.X₃ ⋙ DerivedCategory.Q) K₃ π₃ ∧
        ∀ n : ℕ, β ≫ π₃ n = π₂ n ≫ DerivedCategory.Q.map (S.g.app ⟨n⟩) := by
  obtain ⟨p₁, p₂, p₃, hR₁, hR₂, hR₃, δ, hδ⟩ :=
    isDerivedLimitWithProjections_triangle_of_shortExact S hS h₁ h₂ h₃
  obtain ⟨e₁, he₁⟩ := NoetherianAdicCompletion.exists_iso_of_isDerivedLimitWithProjections hK₁ hR₁
  obtain ⟨e₂, he₂⟩ := NoetherianAdicCompletion.exists_iso_of_isDerivedLimitWithProjections hK₂ hR₂
  -- The separation hypothesis makes the comparison square commute.
  have hsq : α ≫ e₂.hom = e₁.hom ≫ DerivedCategory.Q.map (limMap S.f) := by
    have hzero : ∀ n : ℕ,
        (α - e₁.hom ≫ DerivedCategory.Q.map (limMap S.f) ≫ e₂.inv) ≫ π₂ n = 0 := by
      intro n
      rw [Preadditive.sub_comp, hα n, Category.assoc, Category.assoc, ← he₂ n,
        Iso.inv_hom_id_assoc, iso_hom_comp_Q_map_limMap_comp_Q_map_limit_π _ e₁ _ he₁, sub_self]
    have := hsep _ hzero
    rw [sub_eq_zero] at this
    rw [this, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Complete the square to a morphism of triangles and invert its third component.
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _ hT hδ e₁.hom e₂.hom
    (by simpa using hsq)
  have hiso : IsIso c := by
    refine isIso₃_of_isIso₁₂ (Triangle.homMk _ _ e₁.hom e₂.hom c (by simpa using hsq) hc₂ hc₃)
      hT hδ ?_ ?_
    · exact inferInstanceAs (IsIso e₁.hom)
    · exact inferInstanceAs (IsIso e₂.hom)
  refine ⟨fun n ↦ c ≫ DerivedCategory.Q.map (limit.π S.X₃ ⟨n⟩),
    NoetherianAdicCompletion.isDerivedLimitWithProjections_of_iso hR₃ (asIso c) (fun n ↦ rfl),
    fun n ↦ ?_⟩
  rw [← Category.assoc,
    show β ≫ c = e₂.hom ≫ DerivedCategory.Q.map (limMap S.g) from hc₂, Category.assoc,
    iso_hom_comp_Q_map_limMap_comp_Q_map_limit_π _ e₂ _ he₂]

/-! ### Cohomology of the strictified `Rlim` -/

/-- **The cohomology of the strictified `Rlim` is the limit of the cohomologies**, in a degree
`r` below which the terms have no cohomology. For a tower of cochain complexes of `A`-modules
with epimorphic transition maps whose terms have vanishing cohomology in degree `r - 1`, the
map `Hʳ(Q(lim F)) ⟶ lim Hʳ(Q Fₙ)` induced by the limit projections is an isomorphism.

`Q(lim F)` is a derived limit of `F ⋙ Q` with the images of the limit projections as its
projections (`DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi`), so its degree-`r`
cohomology sits in the Milnor short exact sequence
`0 ⟶ R¹lim H^{r-1}(Q Fₙ) ⟶ Hʳ(Q(lim F)) ⟶ lim Hʳ(Q Fₙ) ⟶ 0` of
`DerivedCategory.exists_milnor_shortExact_of_distTriang`, whose right-hand map is characterized
by those projections and is therefore the map of the statement. The left-hand term is a quotient
of a product of zero modules. -/
public theorem isIso_limitLift_homology_Q_limit_of_epi
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ)
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)] (r : ℤ)
    (h : ∀ n : ℕ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) (r - 1)).obj
      (DerivedCategory.Q.obj (F.obj ⟨n⟩)))) :
    IsIso (limit.lift ((F ⋙ DerivedCategory.Q) ⋙ DerivedCategory.homologyFunctor _ r)
      ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} A) r).mapCone
        (limit.cone F))) := by
  obtain ⟨hprod, δ, hδ⟩ := isDerivedLimitWithProjections_Q_limit_of_epi F
  obtain ⟨e, i, q, w, -, -, hq, hse⟩ :=
    exists_milnor_shortExact_of_distTriang (F ⋙ DerivedCategory.Q) _ _ δ hδ r
  have hqeq : q = limit.lift ((F ⋙ DerivedCategory.Q) ⋙ DerivedCategory.homologyFunctor _ r)
      ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} A) r).mapCone
        (limit.cone F)) := by
    refine limit.hom_ext fun j ↦ ?_
    obtain ⟨n⟩ := j
    rw [hq n, limit.lift_π, ← Functor.map_comp, Pi.lift_π]
    rfl
  subst hqeq
  have hP : IsZero (∏ᶜ fun n : ℕ ↦ ((F ⋙ DerivedCategory.Q) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{v} A) (r - 1)).obj (Opposite.op n)) :=
    isZero_limit_of_forall_isZero _ fun j ↦ h j.as
  have hi : i = 0 := (isZero_cokernel_of_isZero hP _).eq_of_src _ _
  have : Mono (ShortComplex.mk i _ w).g := hse.exact.mono_g hi
  have : Epi (ShortComplex.mk i _ w).g := hse.epi_g
  exact isIso_of_mono_of_epi (ShortComplex.mk i _ w).g

end DerivedCategory


end
