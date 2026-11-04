module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import StacksFrontier.CategoryTheory.Limits.SystemColimitMono

/-!
# The four lemmas for colimits of systems in an abelian category

Let `I` be a preordered set and let `(A, T)` be a system over `I` in the sense of
`CategoryTheory.Limits.IsSystemColimit`, satisfying the cocycle condition, with values in an
abelian category `𝒞`. A family of maps `ψ i : A i ⟶ B` compatible with the transition maps
induces a comparison map from the colimit of the system to `B`, and `ψ` exhibits `B` as the
colimit of the system exactly when that comparison is an isomorphism. The colimit is the colimit
of the functor `CategoryTheory.Limits.SystemLift.functor` on the filtered category
`CategoryTheory.Limits.SystemLift I`.

When colimits of shape `SystemLift I` are exact in `𝒞` — for instance when `I` is directed and
`𝒞` satisfies AB5 — the colimit of a sequence of systems which is exact at every index is exact,
and the four lemma of abelian categories applies to the comparison maps. This gives the two
halves of the five lemma for colimits of systems: the comparison map at the middle term is an
epimorphism, respectively a monomorphism, as soon as the comparison maps at its neighbours are
suitably epimorphisms and monomorphisms. Unlike
`CategoryTheory.Limits.IsSystemColimit.exists_eq_of_exact`, which is elementwise and so restricted
to abelian groups, this applies to sheaves.

## Main definitions

* `CategoryTheory.Limits.SystemLift.colimitDesc`: the comparison map from the colimit of a system
  to the vertex of a compatible family of maps.

## Main results

* `CategoryTheory.Limits.SystemLift.isSystemColimit_iff_isIso_colimitDesc`: a compatible family
  exhibits a colimit of the system exactly when its comparison map is an isomorphism.
* `CategoryTheory.Limits.SystemLift.epi_colimitDesc_of_exact` and
  `CategoryTheory.Limits.SystemLift.mono_colimitDesc_of_exact`: **the four lemmas for colimits of
  systems** in an abelian category with exact colimits of shape `SystemLift I`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits.SystemLift

universe w v u

variable {I : Type w} [Preorder I] {𝒞 : Type u} [Category.{v} 𝒞]

section Desc

variable [HasColimitsOfShape (SystemLift I) 𝒞] {A : Iᵒᵖ → 𝒞}
  {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)}
  (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)
  {B : 𝒞} (ψ : ∀ i, A i ⟶ B) (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j)

/-- **The comparison map from the colimit of a system** to the vertex `B` of a family of maps
`ψ i : A i ⟶ B` compatible with the transition maps. -/
def colimitDesc : colimit (functor A T hT) ⟶ B :=
  colimit.desc _ (cocone hT ψ hψ)

/-- The comparison map `colimitDesc hT ψ hψ` restricts along the colimit inclusion at
`x : SystemLift I` to the leg `ψ` at the index of `x`. -/
@[reassoc (attr := simp)]
theorem ι_colimitDesc (x : SystemLift I) :
    colimit.ι (functor A T hT) x ≫ colimitDesc hT ψ hψ = ψ (Opposite.op x.idx) :=
  colimit.ι_desc _ _

/-- **A compatible family exhibits the colimit of a system exactly when its comparison map is an
isomorphism.** -/
theorem isSystemColimit_iff_isIso_colimitDesc :
    IsSystemColimit A T B ψ ↔ IsIso (colimitDesc hT ψ hψ) := by
  rw [isSystemColimit_iff hT ψ hψ]
  refine ⟨fun ⟨hc⟩ => ?_, fun h => ⟨IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (@asIso _ _ _ _ (colimitDesc hT ψ hψ) h) (ι_colimitDesc hT ψ hψ))⟩⟩
  have e : ((colimit.isColimit (functor A T hT)).coconePointUniqueUpToIso hc).hom =
      colimitDesc hT ψ hψ := colimit.hom_ext fun x =>
    (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ x).trans (ι_colimitDesc hT ψ hψ x).symm
  rw [← e]
  exact Iso.isIso_hom _

/-- The comparison maps of two systems commute with the colimit of a map of systems and a
compatible map of vertices. -/
@[reassoc]
theorem colim_map_liftNatTrans_comp_colimitDesc {A₂ : Iᵒᵖ → 𝒞}
    {T₂ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₂ j ⟶ A₂ i)}
    (hT₂ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₂ (a ≫ b) = T₂ b ≫ T₂ a)
    {B₂ : 𝒞} {ψ₂ : ∀ i, A₂ i ⟶ B₂} (hψ₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₂ a ≫ ψ₂ i = ψ₂ j)
    (f : ∀ i, A i ⟶ A₂ i) (hf : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ f i = f j ≫ T₂ a)
    (f' : B ⟶ B₂) (hf' : ∀ i, ψ i ≫ f' = f i ≫ ψ₂ i) :
    colim.map (IsSystemColimit.liftNatTrans hT hT₂ f hf) ≫ colimitDesc hT₂ ψ₂ hψ₂ =
      colimitDesc hT ψ hψ ≫ f' :=
  colimit.hom_ext fun x => by
    rw [colim_map, ι_colimMap_assoc, IsSystemColimit.liftNatTrans_app, ι_colimitDesc,
      ι_colimitDesc_assoc]
    exact (hf' _).symm

end Desc

section Four

variable [Abelian 𝒞]

/-- Exactness in a category of functors to an abelian category is detected by evaluations. -/
private theorem shortComplex_exact_of_evaluation {J : Type*} [Category* J]
    (S : ShortComplex (J ⥤ 𝒞)) (h : ∀ j : J, (S.map ((evaluation J 𝒞).obj j)).Exact) :
    S.Exact :=
  S.exact_iff_isZero_homology.mpr <| Functor.isZero _ fun j =>
    ((S.map ((evaluation J 𝒞).obj j)).exact_iff_isZero_homology.mp (h j)).of_iso
      (S.mapHomologyIso ((evaluation J 𝒞).obj j)).symm

variable [HasColimitsOfShape (SystemLift I) 𝒞] [HasExactColimitsOfShape (SystemLift I) 𝒞]
  {A₁ A₂ A₃ : Iᵒᵖ → 𝒞} {T₁ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₁ j ⟶ A₁ i)}
  {T₂ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₂ j ⟶ A₂ i)} {T₃ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₃ j ⟶ A₃ i)}
  (hT₁ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₁ (a ≫ b) = T₁ b ≫ T₁ a)
  (hT₂ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₂ (a ≫ b) = T₂ b ≫ T₂ a)
  (hT₃ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₃ (a ≫ b) = T₃ b ≫ T₃ a)

omit [HasColimitsOfShape (SystemLift I) 𝒞] [HasExactColimitsOfShape (SystemLift I) 𝒞] in
/-- The natural transformations lifting two maps of systems with zero composite compose to
zero. -/
theorem liftNatTrans_comp_eq_zero (f : ∀ i, A₁ i ⟶ A₂ i) (g : ∀ i, A₂ i ⟶ A₃ i)
    (hf : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₁ a ≫ f i = f j ≫ T₂ a)
    (hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₂ a ≫ g i = g j ≫ T₃ a) (hfg : ∀ i, f i ≫ g i = 0) :
    IsSystemColimit.liftNatTrans hT₁ hT₂ f hf ≫ IsSystemColimit.liftNatTrans hT₂ hT₃ g hg = 0 :=
  NatTrans.ext (funext fun _ => hfg _)

/-- **The colimit of a sequence of systems which is exact at every index is exact**, colimits of
shape `SystemLift I` being exact. -/
theorem exact_colim_map_liftNatTrans (f : ∀ i, A₁ i ⟶ A₂ i) (g : ∀ i, A₂ i ⟶ A₃ i)
    (hf : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₁ a ≫ f i = f j ≫ T₂ a)
    (hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₂ a ≫ g i = g j ≫ T₃ a)
    (hfg : ∀ i, f i ≫ g i = 0) (hS : ∀ i, (ShortComplex.mk (f i) (g i) (hfg i)).Exact) :
    (ShortComplex.mk (colim.map (IsSystemColimit.liftNatTrans hT₁ hT₂ f hf))
      (colim.map (IsSystemColimit.liftNatTrans hT₂ hT₃ g hg))
      (by rw [← Functor.map_comp, show IsSystemColimit.liftNatTrans hT₁ hT₂ f hf ≫
          IsSystemColimit.liftNatTrans hT₂ hT₃ g hg = 0 from
          NatTrans.ext (funext fun x => hfg _), Functor.map_zero])).Exact :=
  (shortComplex_exact_of_evaluation (ShortComplex.mk (IsSystemColimit.liftNatTrans hT₁ hT₂ f hf)
    (IsSystemColimit.liftNatTrans hT₂ hT₃ g hg)
    (liftNatTrans_comp_eq_zero hT₁ hT₂ hT₃ f g hf hg hfg)) fun _ => hS _).map colim

end Four

section Four

variable [Abelian 𝒞] [HasColimitsOfShape (SystemLift I) 𝒞]
  [HasExactColimitsOfShape (SystemLift I) 𝒞]
  {A₁ A₂ A₃ A₄ : Iᵒᵖ → 𝒞} {T₁ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₁ j ⟶ A₁ i)}
  {T₂ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₂ j ⟶ A₂ i)} {T₃ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₃ j ⟶ A₃ i)}
  {T₄ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₄ j ⟶ A₄ i)}
  (hT₁ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₁ (a ≫ b) = T₁ b ≫ T₁ a)
  (hT₂ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₂ (a ≫ b) = T₂ b ≫ T₂ a)
  (hT₃ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₃ (a ≫ b) = T₃ b ≫ T₃ a)
  (hT₄ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₄ (a ≫ b) = T₄ b ≫ T₄ a)
  {B₁ B₂ B₃ B₄ : 𝒞} {ψ₁ : ∀ i, A₁ i ⟶ B₁} {ψ₂ : ∀ i, A₂ i ⟶ B₂} {ψ₃ : ∀ i, A₃ i ⟶ B₃}
  {ψ₄ : ∀ i, A₄ i ⟶ B₄}
  (hψ₁ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₁ a ≫ ψ₁ i = ψ₁ j)
  (hψ₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₂ a ≫ ψ₂ i = ψ₂ j)
  (hψ₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₃ a ≫ ψ₃ i = ψ₃ j)
  (hψ₄ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₄ a ≫ ψ₄ i = ψ₄ j)
  (t : ∀ i, A₁ i ⟶ A₂ i) (u : ∀ i, A₂ i ⟶ A₃ i) (v : ∀ i, A₃ i ⟶ A₄ i)
  (ht : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₁ a ≫ t i = t j ≫ T₂ a)
  (hu : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₂ a ≫ u i = u j ≫ T₃ a)
  (hv : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₃ a ≫ v i = v j ≫ T₄ a)
  (t' : B₁ ⟶ B₂) (u' : B₂ ⟶ B₃) (v' : B₃ ⟶ B₄)
  (ht' : ∀ i, ψ₁ i ≫ t' = t i ≫ ψ₂ i) (hu' : ∀ i, ψ₂ i ≫ u' = u i ≫ ψ₃ i)
  (hv' : ∀ i, ψ₃ i ≫ v' = v i ≫ ψ₄ i)

/-- The morphism of four-term rows from the colimits of four systems to the vertices of
compatible families, made of the four comparison maps. -/
private def rowHom :
    ComposableArrows.mk₃ (colim.map (IsSystemColimit.liftNatTrans hT₁ hT₂ t ht))
        (colim.map (IsSystemColimit.liftNatTrans hT₂ hT₃ u hu))
        (colim.map (IsSystemColimit.liftNatTrans hT₃ hT₄ v hv)) ⟶
      ComposableArrows.mk₃ t' u' v' :=
  ComposableArrows.homMk₃ (colimitDesc hT₁ ψ₁ hψ₁) (colimitDesc hT₂ ψ₂ hψ₂)
    (colimitDesc hT₃ ψ₃ hψ₃) (colimitDesc hT₄ ψ₄ hψ₄)
    (colim_map_liftNatTrans_comp_colimitDesc hT₁ _ hψ₁ hT₂ hψ₂ t ht t' ht')
    (colim_map_liftNatTrans_comp_colimitDesc hT₂ _ hψ₂ hT₃ hψ₃ u hu u' hu')
    (colim_map_liftNatTrans_comp_colimitDesc hT₃ _ hψ₃ hT₄ hψ₄ v hv v' hv')

include hψ₁ hψ₂ hψ₃ hψ₄ ht hu hv ht' hu' hv' in
/-- **The four lemma for colimits of systems, epimorphism half.** Let `A₁ → A₂ → A₃ → A₄` be
maps of systems, exact at `A₃` at every index, and `B₁ → B₂ → B₃ → B₄` a complex exact at `B₂`,
compatible with families of legs `ψₖ : Aₖ ⟶ Bₖ`. If the comparison maps of the colimits of the
first and third systems are epimorphisms and the one of the fourth system a monomorphism, then
the comparison map of the second system is an epimorphism. -/
theorem epi_colimitDesc_of_exact (huv : ∀ i, u i ≫ v i = 0)
    (hA : ∀ i, (ShortComplex.mk (u i) (v i) (huv i)).Exact) (ht'u' : t' ≫ u' = 0)
    (hB : (ShortComplex.mk t' u' ht'u').Exact) (hu'v' : u' ≫ v' = 0)
    (h₁ : Epi (colimitDesc hT₁ ψ₁ hψ₁)) (h₃ : Epi (colimitDesc hT₃ ψ₃ hψ₃))
    (h₄ : Mono (colimitDesc hT₄ ψ₄ hψ₄)) : Epi (colimitDesc hT₂ ψ₂ hψ₂) :=
  Abelian.epi_of_epi_of_epi_of_mono'
    (rowHom hT₁ hT₂ hT₃ hT₄ hψ₁ hψ₂ hψ₃ hψ₄ t u v ht hu hv t' u' v' ht' hu' hv')
    (exact_colim_map_liftNatTrans hT₂ hT₃ hT₄ u v hu hv huv hA).exact_toComposableArrows
    hB.exact_toComposableArrows
    (by rwa [(ComposableArrows.mk₃ t' u' v').map'_comp 1 2 3]) h₁ h₃ h₄

include hψ₁ hψ₂ hψ₃ hψ₄ ht hu hv ht' hu' hv' in
/-- **The four lemma for colimits of systems, monomorphism half.** Let `A₁ → A₂ → A₃ → A₄` be
maps of systems, a complex at `A₂` and exact at `A₃` at every index, and `B₁ → B₂ → B₃ → B₄`
exact at `B₂`, compatible with families of legs `ψₖ : Aₖ ⟶ Bₖ`. If the comparison map of the
colimit of the first system is an epimorphism and those of the second and fourth systems are
monomorphisms, then the comparison map of the third system is a monomorphism. -/
theorem mono_colimitDesc_of_exact (htu : ∀ i, t i ≫ u i = 0) (huv : ∀ i, u i ≫ v i = 0)
    (hA : ∀ i, (ShortComplex.mk (u i) (v i) (huv i)).Exact) (ht'u' : t' ≫ u' = 0)
    (hB : (ShortComplex.mk t' u' ht'u').Exact)
    (h₁ : Epi (colimitDesc hT₁ ψ₁ hψ₁)) (h₂ : Mono (colimitDesc hT₂ ψ₂ hψ₂))
    (h₄ : Mono (colimitDesc hT₄ ψ₄ hψ₄)) : Mono (colimitDesc hT₃ ψ₃ hψ₃) :=
  Abelian.mono_of_epi_of_mono_of_mono'
    (rowHom hT₁ hT₂ hT₃ hT₄ hψ₁ hψ₂ hψ₃ hψ₄ t u v ht hu hv t' u' v' ht' hu' hv')
    (by
      show colim.map _ ≫ colim.map _ = 0
      rw [← Functor.map_comp, liftNatTrans_comp_eq_zero hT₁ hT₂ hT₃ t u ht hu htu,
        Functor.map_zero])
    (exact_colim_map_liftNatTrans hT₂ hT₃ hT₄ u v hu hv huv hA).exact_toComposableArrows
    hB.exact_toComposableArrows h₁ h₂ h₄

end Four

end CategoryTheory.Limits.SystemLift
