module

public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonSquareNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentModuleComplex
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# The cotangent complex as a sheafification over a presheaf of base rings

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site, and let `R ⟶ A` be a map
from a *presheaf* of commutative rings which is inverted by sheafification. Over every object `U`
the composite `R(U) → A(U) → B(U)` makes `B(U)` an `R(U)`-algebra. The cotangent complex `L_{B/A}`
is the sheafification of `U ↦ L_{B(U)/R(U)}`; the case `R = A` is
`CategoryTheory.Sheaf.sheafifiedSectionwiseCotangentComplexIso`.

For `A = Λ̲` the constant sheaf and `R` the constant presheaf `U ↦ Λ`, this says that `L_{𝒪_X/Λ̲}`
is the sheafification of `U ↦ L_{𝒪_X(U)/Λ}`, which differs from `U ↦ L_{𝒪_X(U)/Λ̲(U)}` because the
ring `Λ̲(U)` of locally constant functions differs from `Λ` on disconnected `U`.

## Main definitions

* `CategoryTheory.Sheaf.presheafBaseResolutionComparison`: the comparison of the presheaf of rings
  `U ↦ P_n(B(U)/R(U))` with the degree-`n` term of the standard resolution of `A ⟶ B`.
* `CategoryTheory.Sheaf.presheafBaseCotangentTerm`: the presheaf of `B`-modules
  `U ↦ L^j_{B(U)/R(U)}`, and `CategoryTheory.Sheaf.presheafBaseCotangentTermComparison` its
  canonical map to the degree-`j` term of `L_{B/A}`.
* `CategoryTheory.Sheaf.presheafBaseCotangentModuleComplex`: the complex of presheaves of
  `B`-modules `U ↦ L_{B(U)/R(U)}`, and
  `CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentComplex` its degreewise sheafification.

## Main results

* `CategoryTheory.Sheaf.exists_derivation_extension_of_W_base`: derivations over a presheaf of
  base rings into a sheaf extend along a map inverted by sheafification.
* `CategoryTheory.Sheaf.W_presheafBaseResolutionComparison`: the degree-`n` term of the standard
  resolution of `A ⟶ B` is the sheafification of `U ↦ P_n(B(U)/R(U))`.
* `CategoryTheory.Sheaf.isIso_sheafify_presheafBaseCotangentTermComparison`: in every degree `j`
  the term of `L_{B/A}` is the sheafification of `U ↦ L^j_{B(U)/R(U)}`.
* `CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentComplexIso`: the sheafification of the
  complex of presheaves of `B`-modules `U ↦ L_{B(U)/R(U)}` is `L_{B/A}`, and
  `CategoryTheory.Sheaf.sheafifiedPresheafBaseCotangentPresheafComplexIso` the same statement on
  abelian groups.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
attribute [local instance] preservesSheafification_forget_commRingCat
  wEqualsLocallyBijective_commRingCat

/-! ## Derivations over a presheaf of base rings -/

section Derivations

attribute [local instance] moduleOfSections

/-- An `R₀`-derivation `d` of `Q` into a sheaf of `R`-modules `M`, along a map `c : Q ⟶ R` inverted
by sheafification, extends to a family of additive maps `R(U) → M(U)` compatible with the
restriction maps and agreeing with `d` on the image of `c`. -/
private theorem exists_addHom_extension_of_W_base {R : Sheaf J CommRingCat.{max u v w}}
    {R₀ : Cᵒᵖ ⥤ CommRingCat.{max u v w}} (Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (b : R₀ ⟶ Q)
    (c : Q ⟶ R.obj) (hc : J.W c)
    (M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R))
    (d : ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj M.val).Derivation' b) :
    ∃ D : ∀ U, R.obj.obj U →+ M.val.obj U, (∀ U q, D U (c.app U q) = d.d q) ∧
      ∀ {U V} (g : U ⟶ V) (x : R.obj.obj U), M.val.map g (D U x) = D V (R.obj.map g x) := by
  let dAb : Q ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      M.val.presheaf :=
    { app U := AddCommGrpCat.ofHom d.d
      naturality {U V} g := by ext q; exact d.d_map g q }
  let cAb := Functor.whiskerRight c (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  have hcAb : J.W cAb := by
    rw [J.W_iff_isLocallyBijective]
    exact ⟨(Presheaf.isLocallyInjective_forget_iff J cAb).mp
        ((Presheaf.isLocallyInjective_forget_iff J c).mpr hc.isLocallyInjective),
      (Presheaf.isLocallySurjective_iff_whisker_forget J cAb).mpr
        ((Presheaf.isLocallySurjective_iff_whisker_forget J c).mp hc.isLocallySurjective)⟩
  obtain ⟨e, he⟩ := (hcAb M.val.presheaf M.isSheaf).surjective dAb
  exact ⟨fun U => (e.app U).hom,
    fun U q => ConcreteCategory.congr_hom (NatTrans.congr_app he U) q,
    fun g x => (ConcreteCategory.congr_hom (e.naturality g) x).symm⟩

/-- **Derivations into a sheaf extend along a map inverted by sheafification, over a presheaf
of base rings.** Let `a : A ⟶ R` be a homomorphism of sheaves of rings, let `a₀ : R₀ ⟶ A` be a
map from a presheaf of rings which is inverted by sheafification, and let `c : Q ⟶ R` be a map
from a presheaf of rings, inverted by sheafification and compatible with structure maps
`b : R₀ ⟶ Q` and `a₀ ≫ a : R₀ ⟶ R`. Every `R₀`-derivation of `Q` into a sheaf of `R`-modules
extends to an `A`-derivation of `R`. -/
theorem exists_derivation_extension_of_W_base {A R : Sheaf J CommRingCat.{max u v w}}
    (a : A ⟶ R) {R₀ : Cᵒᵖ ⥤ CommRingCat.{max u v w}} (a₀ : R₀ ⟶ A.obj) (ha₀ : J.W a₀)
    (Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (b : R₀ ⟶ Q)
    (c : Q ⟶ R.obj) (hbc : b ≫ c = a₀ ≫ a.hom) (hc : J.W c)
    (M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R))
    (d : ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj M.val).Derivation' b) :
    ∃ D : M.val.Derivation' a.hom, ∀ U q, D.d (c.app U q) = d.d q := by
  have : Presheaf.IsLocallySurjective J c := hc.isLocallySurjective
  obtain ⟨Dadd, heq, enat⟩ := exists_addHom_extension_of_W_base J Q b c hc M d
  let MT : Sheaf J (Type (max u v w)) := (sheafCompose J (forget AddCommGrpCat)).obj
    ((SheafOfModules.toSheaf _).obj M)
  refine ⟨{ d := fun {U} => Dadd U
            d_map := fun g x => (enat g x).symm
            d_app := ?_
            d_mul := ?_ }, heq⟩
  · intro U x y
    let ct := Functor.whiskerRight c (forget CommRingCat)
    have : Presheaf.IsLocallySurjective J ct :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J c).mp inferInstance
    refine eq_of_isLocallySurjective_binary J ct MT
      (fun U (x y : R.obj.obj U) => Dadd U (x * y))
      (fun U (x y : R.obj.obj U) => x • Dadd U y + y • Dadd U x)
      ?_ ?_ ?_ U x y
    · rintro U V g (x : R.obj.obj U) (y : R.obj.obj U)
      show M.val.map g (Dadd U (x * y)) = Dadd V (_ * _)
      rw [enat, map_mul]
      rfl
    · rintro U V g (x : R.obj.obj U) (y : R.obj.obj U)
      have e₁ := M.val.map_smul g x (Dadd U y)
      have e₂ := M.val.map_smul g y (Dadd U x)
      rw [enat] at e₁ e₂
      exact ((M.val.map g).hom.map_add _ _).trans (congrArg₂ (· + ·) e₁ e₂)
    · intro U q r
      show Dadd U (c.app U q * c.app U r) =
        c.app U q • Dadd U (c.app U r) + c.app U r • Dadd U (c.app U q)
      rw [← map_mul, heq, heq, heq]
      exact d.d_mul q r
  · intro U x
    let at₀ := Functor.whiskerRight a₀ (forget CommRingCat)
    have : Presheaf.IsLocallySurjective J at₀ :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J a₀).mp ha₀.isLocallySurjective
    refine eq_of_isLocallySurjective_binary J at₀ MT
      (fun U (x _ : A.obj.obj U) => Dadd U (a.hom.app U x))
      (fun U (_ _ : A.obj.obj U) => (0 : M.val.obj U)) ?_ ?_ ?_ U x x
    · rintro U V g (x : A.obj.obj U) -
      show M.val.map g (Dadd U (a.hom.app U x)) = Dadd V (a.hom.app V (A.obj.map g x))
      rw [enat]
      exact congrArg (Dadd V) (ConcreteCategory.congr_hom (a.hom.naturality g) x).symm
    · rintro U V g - -
      exact map_zero (M.val.map g).hom
    · intro U r _
      show Dadd U (a.hom.app U (a₀.app U r)) = 0
      have hr : a.hom.app U (a₀.app U r) = c.app U (b.app U r) :=
        (ConcreteCategory.congr_hom (NatTrans.congr_app hbc U) r).symm
      rw [hr, heq]
      exact d.d_app r

end Derivations

section Terms

/-! ## Base change from `R` to `A` -/

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)
  {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}} (a : R ⟶ A.obj)

/-- A presheaf of commutative rings, read as a sheaf on the chaotic site `(C, ⊥)`, where every
presheaf is a sheaf. -/
noncomputable abbrev presheafBaseSheaf (P : Cᵒᵖ ⥤ CommRingCat.{max u v w}) :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v w} :=
  ⟨P, Presheaf.isSheaf_bot P⟩

/-- The composite `R ⟶ A ⟶ B`, read as a homomorphism of sheaves on the chaotic site. Over every
`U` it makes `B(U)` an `R(U)`-algebra, and the sectionwise constructions at it are
`U ↦ P_n(B(U)/R(U))` and `U ↦ L_{B(U)/R(U)}`. -/
noncomputable abbrev presheafBaseHom :
    presheafBaseSheaf.{u, v, w} R ⟶ presheafBaseSheaf.{u, v, w} B.obj :=
  ⟨a ≫ f.hom⟩

/-- The commutative square of ring maps `R(U) → A(U)`, `B(U) = B(U)` comparing the `R(U)`-algebra
`B(U)` with the `A(U)`-algebra `B(U)`. -/
noncomputable def presheafBaseSquare (U : Cᵒᵖ) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w}
      ((presheafBaseSheaf.{u, v, w} R).obj.obj U) (A.obj.obj U)
      (sectionsAlgebra ⊥ (presheafBaseHom.{u, v, w} J f a) U)
      (sectionsAlgebra.{u, v, w} J f U) where
  base := (a.app U).hom
  map := RingHom.id _
  map_algebraMap _ := rfl

/-- The base-change squares are natural in `U`: composed with the restriction squares they give
the same square from `R(U) → B(U)` to `A(V) → B(V)`. -/
theorem presheafBaseSquare_naturality {U V : Cᵒᵖ} (g : U ⟶ V) :
    (sectionsRestrictionSquare ⊥ (presheafBaseHom.{u, v, w} J f a) g).comp
        (presheafBaseSquare.{u, v, w} J f a V) =
      (presheafBaseSquare.{u, v, w} J f a U).comp (sectionsRestrictionSquare.{u, v, w} J f g) := by
  have h := congrArg CommRingCat.Hom.hom (a.naturality g)
  unfold CommAlgCat.AlgebraSquare.comp presheafBaseSquare sectionsRestrictionSquare
  congr 1

/-! ## The comparison of standard resolutions -/

/-- **A map of freely generated presheaves of rings with generators inverted by sheafification is
inverted by sheafification.** Let `Q` be freely generated over `R` by a presheaf of sets `P`, and
`Q'` over `R'` by `P'`, in the sense that maps out of them into any presheaf of rings are maps out
of the base together with maps out of the generators. A map `c : Q ⟶ Q'` compatible with maps
`R ⟶ R'` and `P ⟶ P'` that are inverted by sheafification is inverted by sheafification. -/
theorem W_of_bijective_presheafHom {R R' Q Q' : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    {P P' : Cᵒᵖ ⥤ Type (max u v w)} (b : R ⟶ Q) (x : P ⟶ Q ⋙ forget _)
    (b' : R' ⟶ Q') (x' : P' ⟶ Q' ⋙ forget _) (ρ : R ⟶ R') (π : P ⟶ P') (c : Q ⟶ Q')
    (hρ : J.W ρ) (hπ : J.W π) (hb : b ≫ c = ρ ≫ b')
    (hx : x ≫ Functor.whiskerRight c (forget _) = π ≫ x')
    (hQ : ∀ T : Cᵒᵖ ⥤ CommRingCat.{max u v w}, Function.Bijective
      (fun g : Q ⟶ T => (b ≫ g, x ≫ Functor.whiskerRight g (forget _))))
    (hQ' : ∀ T : Cᵒᵖ ⥤ CommRingCat.{max u v w}, Function.Bijective
      (fun g : Q' ⟶ T => (b' ≫ g, x' ≫ Functor.whiskerRight g (forget _)))) :
    J.W c := by
  intro T hT
  have hΨ := Function.Bijective.prodMap (hρ T hT)
    (hπ _ ((sheafForget J).obj (⟨T, hT⟩ : Sheaf J CommRingCat.{max u v w})).property)
  have key : (fun g : Q ⟶ T => (b ≫ g, x ≫ Functor.whiskerRight g (forget _))) ∘
      (fun g : Q' ⟶ T => c ≫ g) =
      Prod.map (fun s : R' ⟶ T => ρ ≫ s) (fun t : P' ⟶ T ⋙ forget _ => π ≫ t) ∘
        (fun g : Q' ⟶ T => (b' ≫ g, x' ≫ Functor.whiskerRight g (forget _))) := by
    funext g
    refine Prod.ext ?_ ?_
    · show b ≫ c ≫ g = ρ ≫ b' ≫ g
      rw [reassoc_of% hb]
    · show x ≫ Functor.whiskerRight (c ≫ g) (forget _) =
        π ≫ x' ≫ Functor.whiskerRight g (forget _)
      rw [Functor.whiskerRight_comp, reassoc_of% hx]
  exact ((hQ T).of_comp_iff' _).mp (key ▸ hΨ.comp (hQ' T))

/-- The map `U ↦ (R(U)[R(U)[⋯[B(U)]⋯]] ⟶ A(U)[A(U)[⋯[B(U)]⋯]])` of stage `n` of the towers of
iterated polynomial algebras, induced by the base-change squares. -/
noncomputable def presheafBaseTowerMap (n : ℕ) :
    sectionwiseTowerPresheaf ⊥ (presheafBaseHom.{u, v, w} J f a) n ⟶
        sectionwiseTowerPresheaf.{u, v, w} J f n where
  app U := CommRingCat.ofHom (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
    (presheafBaseSquare.{u, v, w} J f a U) n)
  naturality {U V} g := by
    apply CommRingCat.hom_ext
    change (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
        (presheafBaseSquare.{u, v, w} J f a V) n).comp
          (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare ⊥ (presheafBaseHom.{u, v, w} J f a) g) n) =
      (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare.{u, v, w} J f g) n).comp
          (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
            (presheafBaseSquare.{u, v, w} J f a U) n)
    rw [← CommAlgCat.standardTowerMap_comp, ← CommAlgCat.standardTowerMap_comp,
      presheafBaseSquare_naturality]

/-- The tower map is compatible with the structure maps from `R` and from `A`. -/
theorem sectionwiseTowerBase_comp_presheafBaseTowerMap (n : ℕ) :
    sectionwiseTowerBase ⊥ (presheafBaseHom.{u, v, w} J f a) n ≫
        presheafBaseTowerMap.{u, v, w} J f a (n + 1) =
      a ≫ sectionwiseTowerBase.{u, v, w} J f n := by
  ext U r
  exact CommAlgCat.standardTowerMap_algebraMap.{max u v w, max u v w, max u v w}
    (presheafBaseSquare.{u, v, w} J f a U) (n + 1) r

/-- The tower map sends variables to variables. -/
theorem sectionwiseTowerVariable_comp_presheafBaseTowerMap (n : ℕ) :
    sectionwiseTowerVariable ⊥ (presheafBaseHom.{u, v, w} J f a) n ≫
        Functor.whiskerRight (presheafBaseTowerMap.{u, v, w} J f a (n + 1)) (forget _) =
      Functor.whiskerRight (presheafBaseTowerMap.{u, v, w} J f a n) (forget _) ≫
        sectionwiseTowerVariable.{u, v, w} J f n := by
  ext U q
  exact CommAlgCat.standardTowerMap_standardTowerX.{max u v w, max u v w, max u v w}
    (presheafBaseSquare.{u, v, w} J f a U) n q

/-- At stage zero the tower map is invertible: both sides are `B`. -/
instance isIso_presheafBaseTowerMap_zero : IsIso (presheafBaseTowerMap.{u, v, w} J f a 0) := by
  have : ∀ U, IsIso ((presheafBaseTowerMap.{u, v, w} J f a 0).app U) := fun U =>
    ⟨CommRingCat.ofHom (RingHom.id _), by ext; rfl, by ext; rfl⟩
  exact NatIso.isIso_of_isIso_app _

/-- **The tower map is inverted by sheafification**, as soon as `R ⟶ A` is. -/
theorem W_presheafBaseTowerMap (ha : J.W a) (n : ℕ) : J.W
    (presheafBaseTowerMap.{u, v, w} J f a n) := by
  induction n with
  | zero => exact ObjectProperty.isLocal_of_isIso _ _
  | succ n ih =>
    exact W_of_bijective_presheafHom J _ _ _ _ a _ _ ha
      (J.W_of_preservesSheafification (forget _) _ ih)
      (sectionwiseTowerBase_comp_presheafBaseTowerMap.{u, v, w} J f a n)
      (sectionwiseTowerVariable_comp_presheafBaseTowerMap.{u, v, w} J f a n)
      (bijective_sectionwiseTowerPresheaf_hom ⊥ (presheafBaseHom.{u, v, w} J f a) n)
      (bijective_sectionwiseTowerPresheaf_hom.{u, v, w} J f n)

/-- The map of presheaves of rings `U ↦ (P_n(B(U)/R(U)) ⟶ P_n(B(U)/A(U)))` of degree-`n` terms of
standard resolutions, induced by the base-change squares. -/
noncomputable def presheafBaseResolutionMap (n : SimplexCategoryᵒᵖ) :
    sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) n ⟶
      sectionwiseResolutionPresheaf.{u, v, w} J f n where
  app U := CommRingCat.ofHom ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (presheafBaseSquare.{u, v, w} J f a U)).resolution n)
  naturality {U V} g := by
    apply CommRingCat.hom_ext
    change ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
        (presheafBaseSquare.{u, v, w} J f a V)).resolution n).comp
          ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare.{u, v, w} ⊥
                (presheafBaseHom.{u, v, w} J f a) g)).resolution n) =
      ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare.{u, v, w} J f g)).resolution n).comp
          ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
            (presheafBaseSquare.{u, v, w} J f a U)).resolution n)
    rw [← CommAlgCat.squareFunctoriality_resolution_comp,
      ← CommAlgCat.squareFunctoriality_resolution_comp, presheafBaseSquare_naturality]

/-- The map of standard resolutions is the tower map, read through the identifications of both
terms with stages of the towers. -/
theorem presheafBaseResolutionMap_eq (n : ℕ) :
    presheafBaseResolutionMap.{u, v, w} J f a (op ⦋n⦌) =
      (sectionwiseResolutionTowerIso.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) n).hom ≫
        presheafBaseTowerMap.{u, v, w} J f a (n + 1) ≫
            (sectionwiseResolutionTowerIso.{u, v, w} J f n).inv := by
  ext U p
  rfl

/-- The map `U ↦ (P_n(B(U)/R(U)) ⟶ P_n(B(U)/A(U)))` is inverted by sheafification. -/
theorem W_presheafBaseResolutionMap (ha : J.W a) (n : SimplexCategoryᵒᵖ) :
    J.W (presheafBaseResolutionMap.{u, v, w} J f a n) := by
  obtain ⟨⟨n⟩⟩ := n
  rw [presheafBaseResolutionMap_eq]
  exact MorphismProperty.comp_mem _ _ _ (ObjectProperty.isLocal_of_isIso _ _)
    (MorphismProperty.comp_mem _ _ _ (W_presheafBaseTowerMap.{u, v, w} J f a ha (n + 1))
      (ObjectProperty.isLocal_of_isIso _ _))

/-- The map of standard resolutions is compatible with the structure maps from `R` and `A`. -/
theorem sectionwiseResolutionBase_comp_presheafBaseResolutionMap (n : SimplexCategoryᵒᵖ) :
    sectionwiseResolutionBase.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) n ≫
        presheafBaseResolutionMap.{u, v, w} J f a n =
      a ≫ sectionwiseResolutionBase.{u, v, w} J f n := by
  ext U r
  exact (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (presheafBaseSquare.{u, v, w} J f a U)).resolution_algebraMap n r

/-- **The comparison of standard resolutions over the base `R`**: the map of presheaves of rings
from `U ↦ P_n(B(U)/R(U))` to the degree-`n` term of the standard resolution of `A ⟶ B`. -/
noncomputable def presheafBaseResolutionComparison (n : SimplexCategoryᵒᵖ) :
    sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) n ⟶
      (resolutionTerm.{u, v, w} J f n).obj :=
  presheafBaseResolutionMap.{u, v, w} J f a n ≫ sectionwiseResolutionComparison.{u, v, w} J f n

/-- **The degree-`n` term of the standard resolution of `A ⟶ B` is the sheafification of
`U ↦ P_n(B(U)/R(U))`**, as soon as `R ⟶ A` is inverted by sheafification. -/
theorem W_presheafBaseResolutionComparison (ha : J.W a) (n : SimplexCategoryᵒᵖ) :
    J.W (presheafBaseResolutionComparison.{u, v, w} J f a n) :=
  MorphismProperty.comp_mem _ _ _ (W_presheafBaseResolutionMap.{u, v, w} J f a ha n)
    (W_sectionwiseResolutionComparison J f n)

/-- The comparison of standard resolutions over `R` is compatible with the structure maps from
`R` and from `A`. -/
theorem sectionwiseResolutionBase_comp_presheafBaseResolutionComparison
    (n : SimplexCategoryᵒᵖ) :
    sectionwiseResolutionBase.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) n ≫
        presheafBaseResolutionComparison.{u, v, w} J f a n = a ≫
            (resolutionBase.{u, v, w} J f n).hom := by
  rw [presheafBaseResolutionComparison,
    reassoc_of% sectionwiseResolutionBase_comp_presheafBaseResolutionMap]
  exact congrArg (a ≫ ·) (sectionwiseResolutionBase_comp_comparison J f n)

/-- The map `L_{B(U)/R(U)} ⟶ L_{B(U)/A(U)}` of the base-change square sends the pure differential
`1 ⊗ d p` to the pure differential of the image of `p`. -/
theorem presheafBaseSquare_sectionsCotangentDifferential (U : Cᵒᵖ) (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w}
      ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
      (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (presheafBaseSquare.{u, v, w} J f a U)).f (-(n : ℤ))
        (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p) =
      sectionsCotangentDifferential'.{u, v, w} J f U n
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (presheafBaseSquare.{u, v, w} J f a U)).resolution (op ⦋n⦌) p) := by
  have h1 := CommAlgCat.squareCotangentComplexMap_degreeIso_inv.{max u v w, max u v w, max u v w}
    (presheafBaseSquare.{u, v, w} J f a U) n
    (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w}
      ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
      (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U) (op ⦋n⦌) p)
  have h2 := CommAlgCat.squareCotangentTermMap_D.{max u v w, max u v w, max u v w}
      (presheafBaseSquare.{u, v, w} J f a U) (op ⦋n⦌) p
  exact h1.trans (congrArg (fun z => (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra.{u, v, w} J f U) n).inv z) h2)

/-! ## The terms of `L_{B/A}` are sheafifications -/

/-- The presheaf of `B`-modules `U ↦ L^j_{B(U)/R(U)}`: the degree-`j` terms of the cotangent
complexes of the ring maps `R(U) → B(U)`, with the maps of the restriction squares as restriction
maps. -/
noncomputable abbrev presheafBaseCotangentTerm (j : ℤ) :
    PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj :=
  sectionwiseCotangentTerm.{u, v, w} ⊥ (presheafBaseHom J f a) j

/-- The map of presheaves of `B`-modules `U ↦ (L^j_{B(U)/R(U)} ⟶ L^j_{B(U)/A(U)})` induced by the
base-change squares. -/
noncomputable def presheafBaseCotangentTermMap (j : ℤ) :
    presheafBaseCotangentTerm.{u, v, w} J f a j ⟶
      sectionwiseCotangentTerm.{u, v, w} J f j where
  app U := (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
      (presheafBaseSquare.{u, v, w} J f a U)).f j
  naturality {U V} g := by
    by_cases hj : 0 < j
    · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w}
        ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
        (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U) j hj).eq_of_src _ _
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      refine sectionsCotangentComplex_hom_ext.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n _ _
        fun p => ?_
      change (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (presheafBaseSquare.{u, v, w} J f a V)).f (-(n : ℤ))
          ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) g)).f
                (-(n : ℤ))
            (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p)) =
        (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare.{u, v, w} J f g)).f (-(n : ℤ))
          ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
            (presheafBaseSquare.{u, v, w} J f a U)).f (-(n : ℤ))
            (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p))
      rw [squareCotangentComplexMap_sectionsCotangentDifferential',
        presheafBaseSquare_sectionsCotangentDifferential,
        presheafBaseSquare_sectionsCotangentDifferential,
        squareCotangentComplexMap_sectionsCotangentDifferential']
      congr 1
      have h := congrArg (fun sq =>
          (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w} sq).resolution
        (op ⦋n⦌) p) (presheafBaseSquare_naturality.{u, v, w} J f a g)
      simp only [CommAlgCat.squareFunctoriality_resolution_comp, RingHom.comp_apply] at h
      exact h

/-- **The canonical map over the base `R`**: from `U ↦ L^j_{B(U)/R(U)}` to the degree-`j` term of
`L_{B/A}`, the change of base `L_{B(U)/R(U)} ⟶ L_{B(U)/A(U)}` followed by the canonical map
`L_{B(U)/A(U)} ⟶ L_{B/A}(U)`. -/
noncomputable def presheafBaseCotangentTermComparison (j : ℤ) :
    presheafBaseCotangentTerm.{u, v, w} J f a j ⟶
      ((cotangentComplex.{u, v, w} J f).X j).val :=
  presheafBaseCotangentTermMap.{u, v, w} J f a j ≫
      sectionwiseCotangentTermComparison.{u, v, w} J f j

/-- Under the canonical map over `R`, the pure differential `1 ⊗ d p` goes to the universal
differential of the image of `p` in `P_n(U)`. -/
theorem presheafBaseCotangentTermComparison_app_differential (n : ℕ) (U : Cᵒᵖ)
    (p : (sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)
        (op ⦋n⦌)).obj U) :
    (presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ))).app U
        (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p) =
      (cotangentComplex_degreeIso.{u, v, w} J f n).inv.val.app U
        ((universalSheafDerivation.{u, v, w} J f (op ⦋n⦌)).d
          ((presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌)).app U p)) :=
  (congrArg ((sectionwiseCotangentTermComparison.{u, v, w} J f (-(n : ℤ))).app U)
    (presheafBaseSquare_sectionsCotangentDifferential.{u, v, w} J f a U n p)).trans
      (sectionwiseCotangentTermComparison_app_differential J f n U _)

/-- The comparison of standard resolutions over `R` carries the augmentation of the standard
resolution of `R(U) → B(U)` to the augmentation of the standard resolution of `A ⟶ B`. -/
theorem presheafBaseResolution_augmentation (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (p : (sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) n).obj U) :
    CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w}
        ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
        (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U) n p =
      (resolutionAugmentation.{u, v, w} J f n).hom.app U
        ((presheafBaseResolutionComparison.{u, v, w} J f a n).app U p) :=
  ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (presheafBaseSquare.{u, v, w} J f a U)).resolution_augmentation
    n p).symm.trans (resolutionAugmentation_resolutionSectionsComparison J f U n _).symm

attribute [local instance] moduleOfSections

/-- The additive components `p ↦ φ(1 ⊗ d p)` of the derivation attached to a map of presheaves of
modules out of `U ↦ L^{-n}_{B(U)/R(U)}`. -/
noncomputable def presheafBaseCotangentTermDerivationAddHom (n : ℕ) (M : targetModules J B)
    (φ : presheafBaseCotangentTerm.{u, v, w} J f a (-(n : ℤ)) ⟶ M.val)
    (U : Cᵒᵖ) : (sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)
        (op ⦋n⦌)).obj U →+ M.val.obj U :=
  AddMonoidHom.comp (M := (CommAlgCat.standardResolution.{max u v w, max u v w}
      ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
      (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U)).left.obj (op ⦋n⦌))
    (N := (CommAlgCat.cotangentComplex.{max u v w, max u v w}
        ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
      (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U)).X (-(n : ℤ)))
    (φ.app U).hom.toAddMonoidHom
    (sectionsCotangentDifferentialAddHom.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n)

/-- The additive components are `p ↦ φ(1 ⊗ d p)`. -/
theorem presheafBaseCotangentTermDerivationAddHom_apply (n : ℕ) (M : targetModules J B)
    (φ : presheafBaseCotangentTerm.{u, v, w} J f a (-(n : ℤ)) ⟶ M.val)
    (U : Cᵒᵖ) (p) :
    presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U p =
      φ.app U (sectionsCotangentDifferential'.{u, v, w} ⊥
        (presheafBaseHom.{u, v, w} J f a) U n p) :=
  rfl

/-- The additive components kill the image of `R`. -/
theorem presheafBaseCotangentTermDerivationAddHom_base (n : ℕ) (M : targetModules J B)
    (φ : presheafBaseCotangentTerm.{u, v, w} J f a (-(n : ℤ)) ⟶ M.val) (U : Cᵒᵖ)
        (r : (presheafBaseSheaf.{u, v, w} R).obj.obj U) :
    presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U
      ((sectionwiseResolutionBase.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)
          (op ⦋n⦌)).app U r) = 0 := by
  rw [presheafBaseCotangentTermDerivationAddHom_apply]
  exact (congrArg (φ.app U)
    (sectionsCotangentDifferential_algebraMap.{u, v, w} ⊥
        (presheafBaseHom.{u, v, w} J f a) U n r)).trans
    (map_zero _)

/-- The additive components are compatible with the restriction maps. -/
theorem presheafBaseCotangentTermDerivationAddHom_map (n : ℕ) (M : targetModules J B)
    (φ : presheafBaseCotangentTerm.{u, v, w} J f a (-(n : ℤ)) ⟶ M.val) {U V : Cᵒᵖ} (g : U ⟶ V)
        (p : (sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)
            (op ⦋n⦌)).obj U) :
    presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ V
        ((sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)
            (op ⦋n⦌)).map g p) =
      M.val.map g (presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U p) := by
  rw [presheafBaseCotangentTermDerivationAddHom_apply,
    presheafBaseCotangentTermDerivationAddHom_apply]
  exact (congrArg (φ.app V)
    (squareCotangentComplexMap_sectionsCotangentDifferential'.{u, v, w} ⊥
      (presheafBaseHom.{u, v, w} J f a) g n p).symm).trans
    (PresheafOfModules.naturality_apply φ g _)

/-- The `R(U)`-derivations of `P_n(B(U)/R(U))` into a sheaf of `B`-modules `M` attached to a map of
presheaves of modules out of `U ↦ L^{-n}_{B(U)/R(U)}`: precompose with `p ↦ 1 ⊗ d p`. -/
noncomputable def presheafBaseCotangentTermDerivation (n : ℕ) (M : targetModules J B)
    (φ : presheafBaseCotangentTerm.{u, v, w} J f a (-(n : ℤ)) ⟶ M.val) :
    ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight (presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌))
        (forget₂ CommRingCat RingCat))).obj
      ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u, v, w} J f (op ⦋n⦌))).obj
        M).val).Derivation'
      (sectionwiseResolutionBase.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) (op ⦋n⦌)) where
  d {U} := presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U
  d_app {U} r := presheafBaseCotangentTermDerivationAddHom_base.{u, v, w} J f a n M φ U r
  d_mul {U} p q := by
    change presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U (p * q) =
      (resolutionAugmentation.{u, v, w} J f (op ⦋n⦌)).hom.app U
          ((presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌)).app U p) •
        presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U q +
      (resolutionAugmentation.{u, v, w} J f (op ⦋n⦌)).hom.app U
          ((presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌)).app U q) •
        presheafBaseCotangentTermDerivationAddHom.{u, v, w} J f a n M φ U p
    rw [presheafBaseCotangentTermDerivationAddHom_apply,
      presheafBaseCotangentTermDerivationAddHom_apply,
      presheafBaseCotangentTermDerivationAddHom_apply]
    refine (congrArg (φ.app U)
      (sectionsCotangentDifferential_mul.{u, v, w} ⊥
          (presheafBaseHom.{u, v, w} J f a) U n p q)).trans ?_
    refine ((φ.app U).hom.map_add _ _).trans ?_
    refine congrArg₂ (· + ·) (((φ.app U).hom.map_smul _ _).trans ?_)
      (((φ.app U).hom.map_smul _ _).trans ?_)
    · exact congrArg (· • φ.app U
        (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n q))
        (presheafBaseResolution_augmentation.{u, v, w} J f a (op ⦋n⦌) U p)
    · exact congrArg (· • φ.app U
        (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p))
        (presheafBaseResolution_augmentation.{u, v, w} J f a (op ⦋n⦌) U q)
  d_map g p := presheafBaseCotangentTermDerivationAddHom_map.{u, v, w} J f a n M φ g p

/-- Every map of presheaves of modules out of `U ↦ L^{-n}_{B(U)/R(U)}` into a sheaf of `B`-modules
factors through the canonical map to the degree-`-n` term of `L_{B/A}`. -/
theorem exists_comp_presheafBaseCotangentTermComparison (ha : J.W a) (n : ℕ)
    (M : targetModules J B)
    (φ : presheafBaseCotangentTerm.{u, v, w} J f a (-(n : ℤ)) ⟶ M.val) :
    ∃ ψ : (cotangentComplex.{u, v, w} J f).X (-(n : ℤ)) ⟶ M,
      presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ)) ≫ ψ.val = φ := by
  obtain ⟨D, hD⟩ := exists_derivation_extension_of_W_base J (resolutionBase.{u, v, w} J f
      (op ⦋n⦌)) a ha
    (sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) (op ⦋n⦌))
    (sectionwiseResolutionBase.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) (op ⦋n⦌))
    (presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌))
    (sectionwiseResolutionBase_comp_presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌))
    (W_presheafBaseResolutionComparison.{u, v, w} J f a ha (op ⦋n⦌))
    ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u, v, w} J f (op ⦋n⦌))).obj M)
    (presheafBaseCotangentTermDerivation.{u, v, w} J f a n M φ)
  refine ⟨(cotangentComplex_degreeIso.{u, v, w} J f n).hom ≫
    ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) M).symm D, ?_⟩
  apply PresheafOfModules.Hom.ext
  funext U
  refine sectionsCotangentComplex_hom_ext.{u, v, w} ⊥
      (presheafBaseHom.{u, v, w} J f a) U n _ _ fun p => ?_
  show (((cotangentComplex_degreeIso.{u, v, w} J f n).hom ≫
      ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) M).symm D).val.app U)
        ((presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ))).app U
          (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p)) = _
  refine (congrArg (fun z => (((cotangentComplex_degreeIso.{u, v, w} J f n).hom ≫
      ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) M).symm D).val.app U) z)
    (presheafBaseCotangentTermComparison_app_differential.{u, v, w} J f a n U p)).trans ?_
  have key : (cotangentComplex_degreeIso.{u, v, w} J f n).inv ≫
      ((cotangentComplex_degreeIso.{u, v, w} J f n).hom ≫
      ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) M).symm D) =
        ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) M).symm D :=
    Iso.inv_hom_id_assoc _ _
  have hd := congrArg (fun h => (((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv
      (op ⦋n⦌) M)
    h).d ((presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌)).app U p)) key
  simp only [Equiv.apply_symm_apply,
    CotangentSimplicialModuleData.derivationEquiv_eq_postcomp] at hd
  exact hd.trans (hD U p)

/-- Two maps out of the degree-`-n` term of `L_{B/A}` into a sheaf of `B`-modules agree as soon as
their composites with the canonical map from `U ↦ L^{-n}_{B(U)/R(U)}` agree. -/
theorem presheafBaseCotangentTermComparison_cancel (ha : J.W a) (n : ℕ)
    (M : targetModules J B) (φ ψ : (cotangentComplex.{u, v, w} J f).X (-(n : ℤ)) ⟶ M)
    (h : presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ)) ≫ φ.val =
      presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ)) ≫ ψ.val) : φ = ψ := by
  refine (cancel_epi (cotangentComplex_degreeIso.{u, v, w} J f n).inv).mp ?_
  refine ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) M).injective ?_
  refine derivation_ext_of_W J (resolutionBase.{u, v, w} J f (op ⦋n⦌))
    (sectionwiseResolutionPresheaf.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) (op ⦋n⦌))
    (presheafBaseResolutionComparison.{u, v, w} J f a (op ⦋n⦌))
    (W_presheafBaseResolutionComparison.{u, v, w} J f a ha (op ⦋n⦌)) _ _ _ fun U p => ?_
  rw [CotangentSimplicialModuleData.derivationEquiv_eq_postcomp,
    CotangentSimplicialModuleData.derivationEquiv_eq_postcomp]
  have he := ConcreteCategory.congr_hom (congrArg (fun k => k.app U) h)
    (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p)
  change φ.val.app U ((presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ))).app U
      (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p)) =
    ψ.val.app U ((presheafBaseCotangentTermComparison.{u, v, w} J f a (-(n : ℤ))).app U
      (sectionsCotangentDifferential'.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U n p)) at he
  have h' := presheafBaseCotangentTermComparison_app_differential.{u, v, w} J f a n U p
  exact (congrArg (φ.val.app U) h').symm.trans (he.trans (congrArg (ψ.val.app U) h'))

/-- Precomposition with the canonical map identifies maps out of the degree-`j` term of `L_{B/A}`
into a sheaf of `B`-modules with maps of presheaves of modules out of `U ↦ L^j_{B(U)/R(U)}`. -/
theorem bijective_presheafBaseCotangentTermComparison_comp (ha : J.W a) (j : ℤ)
    (M : targetModules J B) :
    Function.Bijective (fun ψ : (cotangentComplex.{u, v, w} J f).X j ⟶ M =>
      presheafBaseCotangentTermComparison.{u, v, w} J f a j ≫ ψ.val) := by
  by_cases hj : 0 < j
  · refine ⟨fun φ ψ _ => (cotangentComplex_isZero_pos J f j hj).eq_of_src _ _, fun φ => ⟨0, ?_⟩⟩
    apply PresheafOfModules.Hom.ext
    funext U
    exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w}
      ((presheafBaseSheaf.{u, v, w} R).obj.obj U)
      (sectionsAlgebra.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) U) j hj).eq_of_src _ _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    exact ⟨fun φ ψ h => presheafBaseCotangentTermComparison_cancel.{u, v, w} J f a ha n M φ ψ h,
      exists_comp_presheafBaseCotangentTermComparison.{u, v, w} J f a ha n M⟩

/-- **The terms of `L_{B/A}` over a presheaf of base rings.** Let `R ⟶ A` be a map from a presheaf
of rings to a sheaf of rings that is inverted by sheafification. In every degree `j`, the term of
the cotangent complex `L_{B/A}` is the sheafification of the presheaf of `B`-modules
`U ↦ L^j_{B(U)/R(U)}`, along the canonical maps: the adjunct of the canonical map out of the
sheafification is an isomorphism. -/
theorem isIso_sheafify_presheafBaseCotangentTermComparison (ha : J.W a) (j : ℤ) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
        (presheafBaseCotangentTermComparison.{u, v, w} J f a j)) := by
  let R' := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B
  let P : PresheafOfModules.{max u v w} R'.obj := presheafBaseCotangentTerm.{u, v, w} J f a j
  let L := (cotangentComplex.{u, v, w} J f).X j
  let c := presheafBaseCotangentTermComparison.{u, v, w} J f a j
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v w} (𝟙 R'.obj)
  have he : adj.homEquiv P L =
      PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 R'.obj) :=
    Equiv.ext fun g => PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ g
  rw [← he, isIso_iff_coyoneda_map_bijective]
  intro M
  have hE (ψ : L ⟶ M) :
      adj.homEquiv P M ((adj.homEquiv P L).symm c ≫ ψ) = c ≫ ψ.val := by
    rw [Adjunction.homEquiv_naturality_right]
    exact congrArg (· ≫ _) ((adj.homEquiv P L).apply_symm_apply c)
  have hb := bijective_presheafBaseCotangentTermComparison_comp.{u, v, w} J f a ha j M
  refine ⟨fun φ ψ h => hb.injective
    ((hE φ).symm.trans ((congrArg (adj.homEquiv P M) h).trans (hE ψ))), fun φ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hb.surjective (adj.homEquiv P M φ)
  exact ⟨ψ, (adj.homEquiv P M).injective ((hE ψ).trans hψ)⟩

end Terms

/-! ## The complex `L_{B/A}` is the sheafification of `U ↦ L_{B(U)/R(U)}` -/

section PresheafBaseComplex

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)
  {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}} (a : R ⟶ A.obj)

/-- The presheaf `U ↦ L_{B(U)/R(U)}` as a complex of presheaves of `B`-modules: in degree `j` it is
`CategoryTheory.Sheaf.presheafBaseCotangentTerm`, with the differentials of the cotangent
complexes of the ring maps `R(U) → B(U)`. -/
noncomputable abbrev presheafBaseCotangentModuleComplex :
    CochainComplex (PresheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj) ℤ :=
  sectionwiseCotangentModuleComplex.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)

/-- The canonical maps over the base `R`, as a map of complexes of presheaves of `B`-modules from
`U ↦ L_{B(U)/R(U)}` to the underlying presheaves of `L_{B/A}`. -/
noncomputable def presheafBaseCotangentComplexComparison :
    presheafBaseCotangentModuleComplex.{u, v, w} J f a ⟶
      ((SheafOfModules.forget
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v, w} J f) where
  f j := presheafBaseCotangentTermComparison.{u, v, w} J f a j
  comm' i j _ := by
    ext U x
    have h1 := ConcreteCategory.congr_hom
        ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
      (presheafBaseSquare.{u, v, w} J f a U)).comm i j) x
    have h2 := ConcreteCategory.congr_hom
        ((sectionsCotangentComplexComparison.{u, v, w} J f U).comm i j)
      ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (presheafBaseSquare.{u, v, w} J f a U)).f i x)
    exact h2.trans (congrArg ((sectionsCotangentComplexComparison.{u, v, w} J f U).f j) h1)

/-- The degreewise sheafification of `U ↦ L_{B(U)/R(U)}`, a complex of sheaves of `B`-modules. -/
noncomputable def sheafifiedPresheafBaseCotangentComplex :
    CochainComplex (targetModules J B) ℤ :=
  ((PresheafOfModules.sheafification.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (presheafBaseCotangentModuleComplex.{u, v, w} J f a)

/-- In degree `j`, the sheafification of `U ↦ L^j_{B(U)/R(U)}` is the degree-`j` term of `L_{B/A}`,
by the adjunct of the canonical map. -/
noncomputable def sheafifiedPresheafBaseCotangentTermIso (ha : J.W a) (j : ℤ) :
    (PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).obj
        ((presheafBaseCotangentModuleComplex.{u, v, w} J f a).X j) ≅
      (cotangentComplex.{u, v, w} J f).X j :=
  @asIso _ _ _ _ ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
          (presheafBaseCotangentTermComparison.{u, v, w} J f a j))
    (isIso_sheafify_presheafBaseCotangentTermComparison.{u, v, w} J f a ha j)

/-- **`L_{B/A}` as a sheafification over a presheaf of base rings.** Let `R ⟶ A` be a map from a
presheaf of commutative rings to a sheaf of commutative rings that is inverted by sheafification,
and let `A ⟶ B` be a homomorphism of sheaves of commutative rings. The cotangent complex `L_{B/A}`
is the sheafification of the rule `U ↦ L_{B(U)/R(U)}`: the degreewise sheafification of the complex
of presheaves of `B`-modules `U ↦ L_{B(U)/R(U)}` is isomorphic to `L_{B/A}` as a complex of sheaves
of `B`-modules, in each degree by the adjunct of the canonical map. -/
noncomputable def sheafifiedPresheafBaseCotangentComplexIso (ha : J.W a) :
    sheafifiedPresheafBaseCotangentComplex.{u, v, w} J f a ≅ cotangentComplex.{u, v, w} J f :=
  HomologicalComplex.Hom.isoOfComponents
    (sheafifiedPresheafBaseCotangentTermIso.{u, v, w} J f a ha)
    (fun i j _ => by
      let adj := PresheafOfModules.sheafificationAdjunction.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)
      let K := presheafBaseCotangentModuleComplex.{u, v, w} J f a
      let L := cotangentComplex.{u, v, w} J f
      let c := presheafBaseCotangentTermComparison.{u, v, w} J f a
      have h1 : (adj.homEquiv (K.X i) (L.X j)).symm
          (c i ≫ (SheafOfModules.forget _ ⋙
          PresheafOfModules.restrictScalars
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).map (L.d i j)) =
          (adj.homEquiv (K.X i) (L.X i)).symm (c i) ≫ L.d i j :=
        adj.homEquiv_naturality_right_symm _ _
      have h2 : (adj.homEquiv (K.X i) (L.X j)).symm (K.d i j ≫ c j) =
          (PresheafOfModules.sheafification.{max u v w}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).map (K.d i j) ≫
            (adj.homEquiv (K.X j) (L.X j)).symm (c j) :=
        adj.homEquiv_naturality_left_symm _ _
      have h3 : c i ≫ (SheafOfModules.forget _ ⋙
          PresheafOfModules.restrictScalars
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).map
          (L.d i j) = K.d i j ≫ c j :=
        (presheafBaseCotangentComplexComparison.{u, v, w} J f a).comm i j
      have hs (P : PresheafOfModules.{max u v w}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)
              (M : targetModules J B) :
          (adj.homEquiv P M).symm = (PresheafOfModules.sheafificationHomEquiv.{max u v w}
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm :=
        congrArg Equiv.symm
          (Equiv.ext fun g => PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ g)
      rw [hs, hs] at h1
      rw [hs, hs] at h2
      change (PresheafOfModules.sheafificationHomEquiv.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm (c i) ≫
          L.d i j =
        (PresheafOfModules.sheafification.{max u v w}
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).map (K.d i j) ≫
          (PresheafOfModules.sheafificationHomEquiv.{max u v w}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm (c j)
      exact h1.symm.trans ((congrArg _ h3).trans h2))

/-- In each degree the isomorphism is the adjunct of the canonical map. -/
theorem sheafifiedPresheafBaseCotangentComplexIso_hom_f (ha : J.W a) (j : ℤ) :
    (sheafifiedPresheafBaseCotangentComplexIso.{u, v, w} J f a ha).hom.f j =
      (PresheafOfModules.sheafificationHomEquiv.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
        (presheafBaseCotangentTermComparison.{u, v, w} J f a j) :=
  rfl

/-- A map from a presheaf of modules to a sheaf of modules whose adjunct out of the sheafification
is an isomorphism is, on underlying presheaves of abelian groups, inverted by sheafification. -/
theorem W_toPresheaf_of_isIso_sheafificationHomEquiv_symm
    {O : Sheaf J RingCat.{max u v w}} {P : PresheafOfModules.{max u v w} O.obj}
    {L : SheafOfModules.{max u v w} O} (c : P ⟶ L.val)
    (hc : IsIso ((PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 O.obj)).symm c)) :
    J.W ((PresheafOfModules.toPresheaf _).map c) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv.{max u v w} (𝟙 O.obj)
    ((PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 O.obj)).symm c)
  have h' := (congrArg (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
        (𝟙 O.obj)).apply_symm_apply c)).symm.trans h
  have hX : IsIso ((SheafOfModules.toSheaf O).map
      ((PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 O.obj)).symm c)) :=
    Functor.map_isIso _ _
  exact h' ▸ W_homEquiv_of_isIso J _ _ (hX := hX)

/-- The canonical maps over the base `R`, as a map of complexes of presheaves of abelian groups
from `U ↦ L_{B(U)/R(U)}` to the underlying presheaves of `L_{B/A}`. -/
noncomputable def presheafBaseCotangentPresheafComplexComparison :
    sectionwiseCotangentPresheafComplex.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a) ⟶
      ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplexAb.{u, v, w} J f) where
  f j := (PresheafOfModules.toPresheaf _).map
      (presheafBaseCotangentTermComparison.{u, v, w} J f a j)
  comm' i j _ := by
    ext U x
    have h1 := ConcreteCategory.congr_hom
        ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
      (presheafBaseSquare.{u, v, w} J f a U)).comm i j) x
    have h2 := ConcreteCategory.congr_hom
        ((sectionsCotangentComplexComparison.{u, v, w} J f U).comm i j)
      ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (presheafBaseSquare.{u, v, w} J f a U)).f i x)
    exact h2.trans (congrArg ((sectionsCotangentComplexComparison.{u, v, w} J f U).f j) h1)

/-- In every degree the canonical map from `U ↦ L_{B(U)/R(U)}` to `L_{B/A}` is inverted by
sheafification. -/
theorem W_presheafBaseCotangentPresheafComplexComparison_f (ha : J.W a) (j : ℤ) :
    J.W ((presheafBaseCotangentPresheafComplexComparison.{u, v, w} J f a).f j) :=
  W_toPresheaf_of_isIso_sheafificationHomEquiv_symm J _
    (isIso_sheafify_presheafBaseCotangentTermComparison.{u, v, w} J f a ha j)

/-- The sheafification of the canonical map from `U ↦ L_{B(U)/R(U)}` to `L_{B/A}` is an
isomorphism of complexes of sheaves of abelian groups. -/
theorem isIso_sheafify_presheafBaseCotangentPresheafComplexComparison (ha : J.W a) :
    IsIso (((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
          (presheafBaseCotangentPresheafComplexComparison.{u, v, w} J f a)) := by
  have : ∀ n, IsIso ((((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
          (presheafBaseCotangentPresheafComplexComparison.{u, v, w} J f a)).f n) :=
    fun n => isIso_presheafToSheaf_map_of_W J _
      (W_presheafBaseCotangentPresheafComplexComparison_f J f a ha n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **`L_{B/A}` as a sheafification over a presheaf of base rings, on abelian groups.** The
sheafification of the presheaf of complexes of abelian groups `U ↦ L_{B(U)/R(U)}` is isomorphic to
`L_{B/A}`, by the canonical maps followed by the counit of sheafification, as soon as `R ⟶ A` is
inverted by sheafification. -/
noncomputable def sheafifiedPresheafBaseCotangentPresheafComplexIso (ha : J.W a) :
    ((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentPresheafComplex.{u, v, w} ⊥ (presheafBaseHom.{u, v, w} J f a)) ≅
      cotangentComplexAb.{u, v, w} J f :=
  have := isIso_sheafify_presheafBaseCotangentPresheafComplexComparison J f a ha
  asIso (((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (presheafBaseCotangentPresheafComplexComparison.{u, v, w} J f a)) ≪≫
    (NatIso.mapHomologicalComplex
      (asIso (sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app
            (cotangentComplexAb.{u, v, w} J f)

end PresheafBaseComplex

end CategoryTheory.Sheaf

end
