module

public import StacksFrontier.Deformation.ToposThickening.DerivedLiftAutomorphisms
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftBaseChange
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionBaseChangeConnecting
public import StacksFrontier.Deformation.ToposThickening.FlatTensorAmplitude
public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroReductionBaseChange

/-!
# The automorphisms `1 + t` of a lift under base change

Let `R` and `R'` be reduction triangles of derived base changes along square-zero extensions
`f : O ⟶ O₀` and `f' : O' ⟶ O₀`, and `B` a base change between them
(`Deformation.ComplexLift.DerivedReductionBaseChange`), with functor `β : D(O) ⥤ D(O')` and map
of ideal parts `u : - ⊗^L I ⟶ - ⊗^L I'`. For a lift `L` of `K₀` across `f` and
`t : K₀ ⟶ K₀ ⊗^L I`, the automorphism `1 + t` of `L` (`Deformation.ComplexLift.comparisonHom`,
Stacks 0DIZ (1)) is carried by `β` to the automorphism `1 + (t ≫ u)` of the base-changed lift,
as soon as `β` is left adjoint to a functor `G` through which restriction along `f` factors and the
inclusions of the ideal parts correspond
(`Deformation.ComplexLift.comparisonHom_baseChange_of_idealInclusion`). Moreover `1 + t` is
transported along an isomorphism of lifts when the inclusion of the ideal part is natural
(`Deformation.ComplexLift.comparisonHom_hom_conj_of_isomorphic`).

These are the formal inputs of the naturality in the vector space `V` of the map `g ↦ 1 + g` of
the proof of Stacks 0DLL.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe d d' d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Conj

variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {T : DerivedExtensionOfScalars f}
  {idealTensor : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
  (R : DerivedReduction T idealTensor)
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The automorphism `1 + t` of a lift, written out: the identity plus the transpose of
`α ≫ t ≫ α⁻¹` followed by the inclusion of the ideal part. -/
theorem comparisonHom_hom_eq (L : DerivedLift T K₀)
    (t : Multiplicative (K₀.obj ⟶ idealTensor.obj K₀.obj)) :
    (comparisonHom R L t).asIso.hom = 𝟙 L.K.obj +
      R.adjunction.homEquiv L.K.obj _ (L.identification.hom ≫ Multiplicative.toAdd t ≫
        idealTensor.map L.identification.inv) ≫ R.idealInclusion L.K.obj := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The automorphism `1 + t` is transported along isomorphisms of lifts.** If the inclusion of
the ideal part is natural along `e : L₁ ⟶ L₂`, an isomorphism of lifts of `K₀`, then
`e⁻¹ ∘ (1 + t) ∘ e = 1 + t`. -/
theorem comparisonHom_hom_conj_of_isomorphic (L₁ L₂ : DerivedLift T K₀)
    (e : L₁.K.obj ≅ L₂.K.obj)
    (he : T.baseChange.map e.hom ≫ L₂.identification.hom = L₁.identification.hom)
    (hnat : R.idealInclusion L₁.K.obj ≫ e.hom =
      R.restriction.map (idealTensor.map (T.baseChange.map e.hom)) ≫ R.idealInclusion L₂.K.obj)
    (t : Multiplicative (K₀.obj ⟶ idealTensor.obj K₀.obj)) :
    e.inv ≫ (comparisonHom R L₁ t).asIso.hom ≫ e.hom = (comparisonHom R L₂ t).asIso.hom := by
  have hid₁ : L₁.identification.hom = T.baseChange.map e.hom ≫ L₂.identification.hom := he.symm
  have hid₁' : L₁.identification.inv ≫ T.baseChange.map e.hom = L₂.identification.inv := by
    rw [← cancel_epi L₁.identification.hom, Iso.hom_inv_id_assoc, hid₁, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hy : T.baseChange.map e.inv ≫ (L₁.identification.hom ≫ Multiplicative.toAdd t ≫
        idealTensor.map L₁.identification.inv) ≫ idealTensor.map (T.baseChange.map e.hom) =
      L₂.identification.hom ≫ Multiplicative.toAdd t ≫ idealTensor.map L₂.identification.inv := by
    rw [hid₁, ← hid₁']
    simp only [Category.assoc, Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id_map,
      Category.id_comp]
  have hs : e.inv ≫ R.adjunction.homEquiv L₁.K.obj _ (L₁.identification.hom ≫
        Multiplicative.toAdd t ≫ idealTensor.map L₁.identification.inv) ≫
        R.restriction.map (idealTensor.map (T.baseChange.map e.hom)) =
      R.adjunction.homEquiv L₂.K.obj _ (L₂.identification.hom ≫ Multiplicative.toAdd t ≫
        idealTensor.map L₂.identification.inv) := by
    rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left, hy]
  have key : e.inv ≫ R.adjunction.homEquiv L₁.K.obj _ (L₁.identification.hom ≫
        Multiplicative.toAdd t ≫ idealTensor.map L₁.identification.inv) ≫
        R.idealInclusion L₁.K.obj ≫ e.hom =
      R.adjunction.homEquiv L₂.K.obj _ (L₂.identification.hom ≫ Multiplicative.toAdd t ≫
        idealTensor.map L₂.identification.inv) ≫ R.idealInclusion L₂.K.obj := by
    rw [hnat, ← hs]
    simp only [Category.assoc]
  rw [comparisonHom_hom_eq, comparisonHom_hom_eq, Preadditive.add_comp, Preadditive.comp_add,
    Category.id_comp, Iso.inv_hom_id]
  exact congrArg (𝟙 _ + ·) ((congrArg (e.inv ≫ ·) (Category.assoc _ _ _)).trans key)

end Conj

section BaseChange

variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {T : DerivedExtensionOfScalars f} {T' : DerivedExtensionOfScalars f'}
  {idealTensor idealTensor' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
  {R : DerivedReduction T idealTensor} {R' : DerivedReduction T' idealTensor'}
  (B : DerivedReductionBaseChange R R')
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The base change of the automorphism `1 + t` of a lift is `1 + (t ≫ u)`.** Let `β ⊣ G` be
an adjunction `D(O) ⇄ D(O')` with the functor of the base change `B` as left adjoint,
`ρ : G ∘ (restriction along f') ≅ restriction along f`, such that the transpose along `f` of
`φ⁻¹ ≫ x` is the transpose along `f'` and then along `β ⊣ G` of `x` (`φ` the identification of
the base changes to `O₀` of `B`). If the inclusion of the ideal part of `L.K` followed by the
unit of `β ⊣ G` is, through `ρ` and the map of ideal parts `u` of `B`, the inclusion of the ideal
part of `β L.K`, then `β (1 + t) = 1 + (t ≫ u)` on the base-changed lift `β L`. -/
theorem comparisonHom_baseChange_of_idealInclusion
    {G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    [G.Additive] (adj : B.functor ⊣ G) (ρ : R'.restriction ⋙ G ≅ R.restriction)
    (hφ : ∀ (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
      (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
      (x : T'.baseChange.obj (B.functor.obj K) ⟶ Y),
      R.adjunction.homEquiv K Y (B.baseChangeIso.inv.app K ≫ x) =
        adj.homEquiv K _ (R'.adjunction.homEquiv _ Y x) ≫ ρ.hom.app Y)
    (L : DerivedLift T K₀)
    (hι : R.idealInclusion L.K.obj ≫ adj.unit.app L.K.obj =
      R.restriction.map (B.idealMap.app (T.baseChange.obj L.K.obj) ≫
          idealTensor'.map (B.baseChangeIso.inv.app L.K.obj)) ≫
        ρ.inv.app _ ≫ G.map (R'.idealInclusion (B.functor.obj L.K.obj)))
    (t : Multiplicative (K₀.obj ⟶ idealTensor.obj K₀.obj)) :
    B.functor.map (comparisonHom R L t).asIso.hom =
      (comparisonHom R' (L.baseChange B)
        (Multiplicative.ofAdd (Multiplicative.toAdd t ≫ B.idealMap.app K₀.obj))).asIso.hom := by
  -- the two automorphisms, written out on `L.K` and `β L.K`
  let y : T.baseChange.obj L.K.obj ⟶ idealTensor.obj (T.baseChange.obj L.K.obj) :=
    L.identification.hom ≫ Multiplicative.toAdd t ≫ idealTensor.map L.identification.inv
  let m : idealTensor.obj (T.baseChange.obj L.K.obj) ⟶
      idealTensor'.obj (T'.baseChange.obj (B.functor.obj L.K.obj)) :=
    B.idealMap.app (T.baseChange.obj L.K.obj) ≫ idealTensor'.map (B.baseChangeIso.inv.app L.K.obj)
  let y' : T'.baseChange.obj (B.functor.obj L.K.obj) ⟶
      idealTensor'.obj (T'.baseChange.obj (B.functor.obj L.K.obj)) :=
    (B.baseChangeIso.hom.app L.K.obj ≫ L.identification.hom) ≫
      (Multiplicative.toAdd t ≫ B.idealMap.app K₀.obj) ≫
      idealTensor'.map (L.identification.inv ≫ B.baseChangeIso.inv.app L.K.obj)
  have hL : (comparisonHom R L t).asIso.hom = 𝟙 L.K.obj +
      R.adjunction.homEquiv L.K.obj _ y ≫ R.idealInclusion L.K.obj := rfl
  have hL' : (comparisonHom R' (L.baseChange B)
        (Multiplicative.ofAdd (Multiplicative.toAdd t ≫ B.idealMap.app K₀.obj))).asIso.hom =
      𝟙 (B.functor.obj L.K.obj) + R'.adjunction.homEquiv (B.functor.obj L.K.obj) _ y' ≫
        R'.idealInclusion (B.functor.obj L.K.obj) := rfl
  have hy : B.baseChangeIso.inv.app L.K.obj ≫ y' = y ≫ m := by
    have hu := B.idealMap.naturality L.identification.inv
    simp only [y, y', m, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp] at hu ⊢
    rw [reassoc_of% hu]
  have hs : adj.homEquiv L.K.obj _ (R'.adjunction.homEquiv _ _ y') =
      R.adjunction.homEquiv L.K.obj _ y ≫ R.restriction.map m ≫ ρ.inv.app _ := by
    rw [← Category.assoc, ← Adjunction.homEquiv_naturality_right, ← hy, hφ, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h1 : ∀ x : L.K.obj ⟶ L.K.obj,
      adj.homEquiv _ _ (B.functor.map x) =
        x ≫ adj.homEquiv _ _ (𝟙 (B.functor.obj L.K.obj)) := fun x => by
    rw [← Adjunction.homEquiv_naturality_left, Category.comp_id]
  have h2 : ∀ (s' : B.functor.obj L.K.obj ⟶ R'.restriction.obj
      (idealTensor'.obj (T'.baseChange.obj (B.functor.obj L.K.obj)))),
      adj.homEquiv _ _ (𝟙 (B.functor.obj L.K.obj) + s' ≫
          R'.idealInclusion (B.functor.obj L.K.obj)) =
        adj.homEquiv _ _ (𝟙 (B.functor.obj L.K.obj)) +
          adj.homEquiv _ _ s' ≫ G.map (R'.idealInclusion (B.functor.obj L.K.obj)) := fun s' => by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_add, Preadditive.comp_add, Functor.map_comp, Category.assoc]
  apply (adj.homEquiv _ _).injective
  have hu1 : adj.homEquiv _ _ (𝟙 (B.functor.obj L.K.obj)) = adj.unit.app L.K.obj := by
    simp [Adjunction.homEquiv_unit]
  rw [hL, hL', h1, h2, hs, Preadditive.add_comp, Category.id_comp, Category.assoc,
    Category.assoc, hu1, hι]
  simp only [Category.assoc]
  rfl

end BaseChange

/-! ### The inclusions of the ideal parts under base change -/

/-- A relation between the inclusion of the ideal part along `f`, the unit along `g` and the
inclusion of the ideal part along `f'`, through a functor `G`: the first vertex under base change
(`hc`), the naturality of the comparison of `G` with the degreewise functor (`hf`), the
compatibility of the degreewise inclusions with the degreewise unit (`hd`), and the unit read
degreewise (`he`). The objects are abstract, so that the different spellings of the same object
meet only when the lemma is applied. -/
theorem idealInclusion_chain_eq {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D)
    {A Q₁ K A₂ Y_Z Y_P : D} {A₃ Z P' K' : D'}
    (ι₁ : A ⟶ K) (v₀ v : A ⟶ Q₁) (i : Q₁ ⟶ K) (w : K ⟶ K) (hι₁ : ι₁ = v₀ ≫ i ≫ w)
    (hv : v₀ = v) (hw : w = 𝟙 K)
    (ι₂ : A₃ ⟶ K') (x₀ x : A₃ ⟶ Z) (i' : Z ⟶ P') (c' : P' ⟶ K') (hι₂ : ι₂ = x₀ ≫ i' ≫ c')
    (hx : x₀ = x)
    (η : K ⟶ G.obj K') (Mm : A ⟶ A₂) (ρ : A₂ ⟶ G.obj A₃)
    (fZ : G.obj Z ⟶ Y_Z) (fP : G.obj P' ⟶ Y_P) (fPinv : Y_P ⟶ G.obj P') (q : Y_Z ⟶ Y_P)
    (b : Q₁ ⟶ Y_Z) (e : K ⟶ Y_P)
    (hc : Mm ≫ ρ ≫ G.map x ≫ fZ = v ≫ b) (hf : G.map i' ≫ fP = fZ ≫ q)
    (hfP : fP ≫ fPinv = 𝟙 _) (hd : b ≫ q = i ≫ e) (he : η = e ≫ fPinv ≫ G.map c') :
    ι₁ ≫ η = Mm ≫ ρ ≫ G.map ι₂ := by
  subst hι₁ hv hw hι₂ hx he
  have h1 : G.map i' = fZ ≫ q ≫ fPinv := by
    rw [← reassoc_of% hf, hfP, Category.comp_id]
  simp only [Functor.map_comp, h1, Category.assoc]
  rw [reassoc_of% hc, reassoc_of% hd, Category.id_comp]

/-- A morphism followed by the image of the inverse of an isomorphism and then of the
isomorphism itself. -/
theorem comp_map_inv_comp_map {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D)
    {X Y : D} {Z W : D'} (a : X ⟶ Y) (b : Y ⟶ G.obj Z) (c : W ⟶ Z) [IsIso c] :
    (a ≫ b ≫ G.map (inv c)) ≫ G.map c = a ≫ b := by
  simp

/-- The comparison of the inclusions of the ideal parts is natural: from its value at `K₁` and
the naturality of its factors along `ε : K₁ ⟶ K` (`E` being an epimorphism), its value at `K`.
The objects are abstract, so that the different spellings of the same object meet only when the
lemma is applied. -/
theorem idealInclusion_naturality_chain {D D' : Type*} [Category D] [Category D'] (G : D' ⥤ D)
    {A₁ A K₁ K B₁ B' : D} {K₁' K' C₁ C : D'}
    (E : A₁ ⟶ A) [Epi E] (ι₁ : A₁ ⟶ K₁) (ι : A ⟶ K) (ε : K₁ ⟶ K) (h1 : E ≫ ι = ι₁ ≫ ε)
    (η₁ : K₁ ⟶ G.obj K₁') (η : K ⟶ G.obj K') (ε' : K₁' ⟶ K') (h2 : ε ≫ η = η₁ ≫ G.map ε')
    (M₁ : A₁ ⟶ B₁) (M : A ⟶ B') (Eb : B₁ ⟶ B') (h3 : M₁ ≫ Eb = E ≫ M)
    (ρ₁ : B₁ ⟶ G.obj C₁) (ρ : B' ⟶ G.obj C) (Ec : C₁ ⟶ C) (h4 : ρ₁ ≫ G.map Ec = Eb ≫ ρ)
    (ι₁' : C₁ ⟶ K₁') (ι' : C ⟶ K') (h5 : ι₁' ≫ ε' = Ec ≫ ι')
    (hQ : ι₁ ≫ η₁ = M₁ ≫ ρ₁ ≫ G.map ι₁') :
    ι ≫ η = M ≫ ρ ≫ G.map ι' := by
  refine (cancel_epi E).1 ?_
  rw [reassoc_of% h1, h2, reassoc_of% hQ, ← G.map_comp, h5, G.map_comp, reassoc_of% h4,
    reassoc_of% h3]

section Flat

variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀} (g : O ⟶ O')
  (hg : g ≫ f' = f)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (u₀ : I₀ ⟶ I₀')
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
  (ι' : restrictIdeal f' I₀' ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  (hι' : ι' ≫
    Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f') = 0)
  (hS' : (idealSequenceOf f' I₀' ι' hι').ShortExact)
  (hu : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J g) =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map u₀ ≫
        (restrictScalarsCompIsoOf g hg).inv.app I₀' ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map ι')

include hu in
/-- **The inclusions of the ideal parts under base change**, at the localization of a complex
`P` of flat modules strictly in degrees `≤ n`: the inclusion of the ideal part of `Q(P)` along
`f`, followed by the unit of the derived adjunction along `g`, is the map of ideal parts followed
by the inclusion of the ideal part of the derived base change of `Q(P)` along `f'`, read over `O`
through the identification of the derived restrictions. -/
theorem flatReduction_idealInclusion_comp_unit_Q (n : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    [P.IsStrictlyLE n] (hP : ∀ k, flatObjects O (P.X k)) :
    (flatReduction.{d, d₀} f ι hι hS).idealInclusion (DerivedCategory.Q.obj P) ≫
        (derivedAdjunction.{d, d'} g).unit.app (DerivedCategory.Q.obj P) =
      (restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightMap.{d₀} u₀).app
              ((derivedExtensionOfScalars.{d, d₀} f).obj (DerivedCategory.Q.obj P)) ≫
            (derivedTensorRight.{d₀} I₀').map
              ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app
                (DerivedCategory.Q.obj P))) ≫
        (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
        (restrictionOnDerived.{d, d'} g).map ((flatReduction.{d', d₀} f' ι' hι' hS').idealInclusion
          ((derivedExtensionOfScalars.{d, d'} g).obj (DerivedCategory.Q.obj P))) := by
  have hPc : IsFlatCellular P := isFlatCellular_of_isStrictlyLE O P n hP
  have hP' : ∀ k, flatObjects O' (((extensionOfScalarsCochainComplex J g).obj P).X k) :=
    fun k => flatObjects_extensionOfScalars g (hP k)
  have : ((extensionOfScalarsCochainComplex J g).obj P).IsStrictlyLE n :=
    (CochainComplex.isStrictlyLE_iff _ n).2 fun i hi =>
      (extensionOfScalars g).map_isZero (CochainComplex.isZero_of_isStrictlyLE P n i hi)
  have hP'c : IsFlatCellular ((extensionOfScalarsCochainComplex J g).obj P) :=
    isFlatCellular_of_isStrictlyLE O' _ n hP'
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d'} g P hPc
  have he := derivedAdjunction_unit_app_comp_counit.{d, d'} g P
  refine idealInclusion_chain_eq (restrictionOnDerived.{d, d'} g) _ _
    ((vertexOne.{d, d₀} f I₀).app P) _ _
    (flatReduction_idealInclusion.{d, d₀} f ι hι hS hPc (Iso.refl _))
    ((Iso.hom_comp_eq_id _).1 (vertexOneIso_refl_hom_comp.{d, d₀} f hPc)).symm rfl _ _
    ((restrictionOnDerived.{d', d₀} f').map ((derivedTensorRight.{d₀} I₀').map
      ((derivedExtensionOfScalars.{d', d₀} f').map
        ((derivedExtensionOfScalarsCounit.{d, d'} g).app P))) ≫
      (vertexOne.{d', d₀} f' I₀').app ((extensionOfScalarsCochainComplex J g).obj P)) _ _
    (flatReduction_idealInclusion.{d', d₀} f' ι' hι' hS' hP'c
      (asIso ((derivedExtensionOfScalarsCounit.{d, d'} g).app P)).symm)
    (vertexOneIso_asIso_symm_inv.{d', d₀} f' hP'c _) _ _ _
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
      (((idealPart f' I₀').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex J g).obj P)))
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
      ((extensionOfScalarsCochainComplex J g).obj P))
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.inv.app
      ((extensionOfScalarsCochainComplex J g).obj P))
    (DerivedCategory.Q.map (((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (idealPartInclComplex ι' ((extensionOfScalarsCochainComplex J g).obj P))))
    (DerivedCategory.Q.map (idealPartBaseChangeComplex g hg u₀ P))
    (DerivedCategory.Q.map (extensionUnitComplex g P))
    (vertexOne_baseChange.{d, d', d₀} g hg u₀ P)
    (Functor.mapDerivedCategoryFactors_hom_naturality _ _)
    (Iso.hom_inv_id_app _ _) ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp,
      idealPartBaseChangeComplex_comp_idealPartInclComplex g hg u₀ ι ι' hu P]
  · rw [← cancel_mono ((restrictionOnDerived.{d, d'} g).map
      ((derivedExtensionOfScalarsCounit.{d, d'} g).app P)), he]
    exact (comp_map_inv_comp_map (restrictionOnDerived.{d, d'} g) _ _
      ((derivedExtensionOfScalarsCounit.{d, d'} g).app P)).symm

include hu in
/-- **The inclusions of the ideal parts under base change**, at a bounded above object `K`: the
inclusion of the ideal part of `K` along `f`, followed by the unit of the derived adjunction along
`g`, is the map of ideal parts followed by the inclusion of the ideal part of the derived base
change of `K` along `f'`, read over `O` through the identification of the derived restrictions.
By a resolution of `K` by a complex of flat modules strictly in degrees `≤ n` (Stacks 05T7), where
`Deformation.ComplexLift.flatReduction_idealInclusion_comp_unit_Q` computes it, and naturality. -/
theorem flatReduction_idealInclusion_comp_unit (n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    [K.IsLE n] :
    (flatReduction.{d, d₀} f ι hι hS).idealInclusion K ≫
        (derivedAdjunction.{d, d'} g).unit.app K =
      (restrictionOnDerived.{d, d₀} f).map
          ((derivedTensorRightMap.{d₀} u₀).app ((derivedExtensionOfScalars.{d, d₀} f).obj K) ≫
            (derivedTensorRight.{d₀} I₀').map
              ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K)) ≫
        (restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.app _ ≫
        (restrictionOnDerived.{d, d'} g).map ((flatReduction.{d', d₀} f' ι' hι' hS').idealInclusion
          ((derivedExtensionOfScalars.{d, d'} g).obj K)) := by
  have hK : (DerivedCategory.Q.objPreimage K).IsLE n := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Q.objObjPreimageIso K).symm n
  obtain ⟨L, q, hq, hL, hLE⟩ := (CochainComplex.exists_quasiIso_prop (flatObjects O)
    (flatObjects_cover O) n).2 (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := q)).2 hq
  let e : DerivedCategory.Q.obj L ≅ K := asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso K
  exact idealInclusion_naturality_chain (restrictionOnDerived.{d, d'} g)
    ((restrictionOnDerived.{d, d₀} f).map ((derivedTensorRight.{d₀} I₀).map
      ((derivedExtensionOfScalars.{d, d₀} f).map e.hom))) _ _ _
    (flatReduction_idealInclusion_naturality.{d, d₀} f ι hι hS e.hom).symm _ _ _
    ((derivedAdjunction.{d, d'} g).unit.naturality e.hom) _ _ _
    (functor_map_comp_eq_of_eq (restrictionOnDerived.{d, d₀} f) _ _ _ _
      (derivedTensorRightMap_comp_naturality.{d, d', d₀} g hg u₀ e.hom)).symm _ _ _
    ((restrictionOnDerivedCompIso.{d, d', d₀} g hg).inv.naturality _).symm _ _
    (flatReduction_idealInclusion_naturality.{d', d₀} f' ι' hι' hS'
      ((derivedExtensionOfScalars.{d, d'} g).map e.hom))
    (flatReduction_idealInclusion_comp_unit_Q.{d, d', d₀} g hg u₀ ι hι hS ι' hι' hS' hu n L hL)

end Flat


/-! ### The trivial square-zero extensions -/

section SqZeroExt

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ : Sheaf J CommRingCat.{u}}
  {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (φ : M ⟶ N)
variable [HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ M)))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ N)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- **The base change of `1 + t` along `O₀[M] ⟶ O₀[N]` is `1 + (t ≫ φ)`**: derived extension of
scalars along the map `O₀[M] ⟶ O₀[N]` induced by `φ : M ⟶ N` carries the automorphism `1 + t` of
a lift `L` of `K₀` (`Deformation.ComplexLift.comparisonHom`, Stacks 0DIZ (1)) to the automorphism
`1 + (t ≫ φ)` of the base-changed lift, `φ` acting through the derived map of ideal parts
`- ⊗^L M ⟶ - ⊗^L N`. -/
theorem sqZeroExtReductionBaseChange_comparisonHom
    (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} (sqZeroExtSheafAnySiteProj M)) K₀)
    (t : Multiplicative (K₀.obj ⟶ (derivedTensorRight.{d₀} M).obj K₀.obj)) :
    (sqZeroExtReductionBaseChange.{d, d', d₀} φ).functor.map
        (comparisonHom (sqZeroExtReduction.{d, d₀} M) L t).asIso.hom =
      (comparisonHom (sqZeroExtReduction.{d', d₀} N)
        (L.baseChange (sqZeroExtReductionBaseChange.{d, d', d₀} φ))
        (Multiplicative.ofAdd (Multiplicative.toAdd t ≫
          (sqZeroExtReductionBaseChange.{d, d', d₀} φ).idealMap.app K₀.obj))).asIso.hom := by
  obtain ⟨n, hn⟩ := L.K.property
  have : L.K.obj.IsLE n := hn
  exact comparisonHom_baseChange_of_idealInclusion (sqZeroExtReductionBaseChange.{d, d', d₀} φ)
    (derivedAdjunction.{d, d'} (sqZeroExtSheafAnySiteMap φ))
    (restrictionOnDerivedCompIso.{d, d', d₀} (sqZeroExtSheafAnySiteMap φ)
      (sqZeroExtSheafAnySiteMap_comp_proj φ))
    (derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso.{d, d', d₀}
      (sqZeroExtSheafAnySiteMap φ) (sqZeroExtSheafAnySiteMap_comp_proj φ)) L
    (flatReduction_idealInclusion_comp_unit.{d, d', d₀} (sqZeroExtSheafAnySiteMap φ)
      (sqZeroExtSheafAnySiteMap_comp_proj φ) φ (sqZeroExtIdealInclusion M)
      (sqZeroExtIdealInclusion_comp M) (shortExact_sqZeroExtIdealSequence M)
      (sqZeroExtIdealInclusion N) (sqZeroExtIdealInclusion_comp N)
      (shortExact_sqZeroExtIdealSequence N)
      (sqZeroExtIdealInclusion_comp_unitToRestrictScalarsUnit φ) n L.K.obj) t

/-- **The comparison of a base-changed lift with a lift carries `1 + t` to `1 + (t ≫ φ)`**: for a
lift `L` of `K₀` across `O₀[M] ⟶ O₀` and an isomorphism of lifts `e` from its base change along
`O₀[M] ⟶ O₀[N]` to a lift `L'` across `O₀[N] ⟶ O₀`, the automorphism `1 + t` of `L` base-changed
and transported along `e` is the automorphism `1 + (t ≫ φ)` of `L'`. -/
theorem sqZeroExtReductionBaseChange_comparisonHom_conj
    (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} (sqZeroExtSheafAnySiteProj M)) K₀)
    (L' : DerivedLift (derivedExtensionOfScalarsData.{d', d₀} (sqZeroExtSheafAnySiteProj N)) K₀)
    (e : (sqZeroExtReductionBaseChange.{d, d', d₀} φ).functor.obj L.K.obj ≅ L'.K.obj)
    (he : (derivedExtensionOfScalarsData.{d', d₀} (sqZeroExtSheafAnySiteProj N)).baseChange.map
        e.hom ≫ L'.identification.hom =
      (L.baseChange (sqZeroExtReductionBaseChange.{d, d', d₀} φ)).identification.hom)
    (t : Multiplicative (K₀.obj ⟶ (derivedTensorRight.{d₀} M).obj K₀.obj)) :
    e.symm ≪≫ (sqZeroExtReductionBaseChange.{d, d', d₀} φ).functor.mapIso
        (comparisonHom (sqZeroExtReduction.{d, d₀} M) L t).asIso ≪≫ e =
      (comparisonHom (sqZeroExtReduction.{d', d₀} N) L'
        (Multiplicative.ofAdd (Multiplicative.toAdd t ≫
          (sqZeroExtReductionBaseChange.{d, d', d₀} φ).idealMap.app K₀.obj))).asIso := by
  refine Iso.ext ?_
  refine (congrArg (e.inv ≫ · ≫ e.hom)
    (sqZeroExtReductionBaseChange_comparisonHom.{d, d', d₀} φ L t)).trans ?_
  exact comparisonHom_hom_conj_of_isomorphic (sqZeroExtReduction.{d', d₀} N)
    (L.baseChange (sqZeroExtReductionBaseChange.{d, d', d₀} φ)) L' e he
    (flatReduction_idealInclusion_naturality.{d', d₀} (sqZeroExtSheafAnySiteProj N)
      (sqZeroExtIdealInclusion N) (sqZeroExtIdealInclusion_comp N)
      (shortExact_sqZeroExtIdealSequence N) e.hom) _

end SqZeroExt

end Deformation.ComplexLift

end
