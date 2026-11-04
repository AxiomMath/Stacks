module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Higher direct images and colimits on a locally small site

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor of sites and let `F` be a diagram of sheaves on `𝒞`
with values in an abelian category `𝒜`. If every object of `𝒟` has a covering `{V_i → V}` such
that for every `i` the functor `H^p(u(V_i), -)` preserves the colimit of `F`, then the higher
direct image `R^p f_*` preserves the colimit of `F`.

This is the argument of Stacks 0H7B, which is
`Stacks.Cohomology.HigherDirectImage.preservesColimit_rightDerived_sheafPushforwardContinuous`
for *small* sites and abelian groups. Here the two sites are only locally small — so that the
statement applies to the small étale site of a scheme, whose objects live one universe above its
morphisms — and the coefficients are an arbitrary abelian category, so that it applies to
sheaves of modules. The proof is the source's: by Stacks 072W
(`Stacks.Cohomology.SheafifiedHigherDirectImage.rightDerivedPushforwardIso`) `R^p f_*` is the
sheafification of the presheaf `V ↦ H^p(u(V), -)`, and a cocone of presheaves whose evaluation at
the members of a covering family of every object is a colimit cocone sheafifies to a colimit
cocone of sheaves.

## Main results

All in the namespace `Stacks.Cohomology.HigherDirectImage`:

* `existsUnique_presheafCoconeDesc_of_hasEnoughObjects` and
  `isColimit_presheafToSheaf_mapCocone_of_hasEnoughObjects`: a cocone of presheaves which is
  objectwise a colimit over enough objects sheafifies to a colimit cocone.
* `preservesColimit_rightDerived_sheafPushforwardContinuous_of_hasEnoughObjects`: the local
  criterion for `R^p f_*` to preserve a colimit.

## References

* [Stacks Project, Tag 0H7B](https://stacks.math.columbia.edu/tag/0H7B)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a a' b b' c c' d d'

namespace Stacks.Cohomology.HigherDirectImage

section Sheafification

variable {C : Type d} [Category.{d'} C] {A : Type b} [Category.{b'} A]
  {I : Type c} [Category.{c'} I] {F : I ⥤ (Cᵒᵖ ⥤ A)}

/-- The local descents of two cocones out of a presheaf cocone are compatible with restriction
along a morphism between objects at which the presheaf cocone is a colimit. -/
theorem localDesc_naturality_of_isColimit (coc : Cocone F) (r : Cocone F)
    {U V : C} (f : U ⟶ V)
    (hV : IsColimit (((evaluation Cᵒᵖ A).obj (op V)).mapCocone coc))
    (hU : IsColimit (((evaluation Cᵒᵖ A).obj (op U)).mapCocone coc)) :
    coc.pt.map f.op ≫ hU.desc (((evaluation Cᵒᵖ A).obj (op U)).mapCocone r) =
      hV.desc (((evaluation Cᵒᵖ A).obj (op V)).mapCocone r) ≫ r.pt.map f.op := by
  apply hV.hom_ext
  intro i
  have hUfac := hU.fac (((evaluation Cᵒᵖ A).obj (op U)).mapCocone r) i
  have hVfac := hV.fac (((evaluation Cᵒᵖ A).obj (op V)).mapCocone r) i
  change (coc.ι.app i).app (op U) ≫
    hU.desc (((evaluation Cᵒᵖ A).obj (op U)).mapCocone r) =
    (r.ι.app i).app (op U) at hUfac
  change (coc.ι.app i).app (op V) ≫
    hV.desc (((evaluation Cᵒᵖ A).obj (op V)).mapCocone r) =
    (r.ι.app i).app (op V) at hVfac
  show (coc.ι.app i).app (op V) ≫ coc.pt.map f.op ≫
    hU.desc (((evaluation Cᵒᵖ A).obj (op U)).mapCocone r) =
    (coc.ι.app i).app (op V) ≫
    hV.desc (((evaluation Cᵒᵖ A).obj (op V)).mapCocone r) ≫ r.pt.map f.op
  calc
    _ = ((F.obj i).map f.op ≫ (coc.ι.app i).app (op U)) ≫ _ := by
      rw [← Category.assoc]
      congr 1
      simp
    _ = (F.obj i).map f.op ≫ (r.ι.app i).app (op U) := by rw [Category.assoc, hUfac]
    _ = (r.ι.app i).app (op V) ≫ r.pt.map f.op := by
      simp
    _ = _ := by rw [← hVfac]; simp [Category.assoc]

/-- **The universal property of an objectwise colimit of presheaves against a sheaf.** Let `c` be
a cocone of presheaves which becomes a colimit cocone after evaluation at enough objects of the
site, i.e. at the members of a covering family of every object. Then every compatible family of
maps from the diagram to a sheaf `Y` factors uniquely through `c`. -/
theorem existsUnique_presheafCoconeDesc_of_hasEnoughObjects (K : GrothendieckTopology C)
    (c : Cocone F) (Y : Sheaf K A)
    (η : ∀ i, F.obj i ⟶ Y.obj)
    (hη : ∀ {i j : I} (f : i ⟶ j), F.map f ≫ η j = η i)
    (hEnough : K.HasEnoughObjects
      (fun U => Nonempty (IsColimit (((evaluation Cᵒᵖ A).obj (op U)).mapCocone c)))) :
    ∃! (δ : c.pt ⟶ Y.obj), ∀ i, c.ι.app i ≫ δ = η i := by
  classical
  let r : Cocone F := {
    pt := Y.obj
    ι := { app := η, naturality := fun _ _ f => by simpa using hη f }
  }
  let good : C → Prop := fun U =>
    Nonempty (IsColimit (((evaluation Cᵒᵖ A).obj (op U)).mapCocone c))
  let localDesc (U : C) (hU : good U) : c.pt.obj (op U) ⟶ Y.obj.obj (op U) :=
    (Classical.choice hU).desc (((evaluation Cᵒᵖ A).obj (op U)).mapCocone r)
  have localDesc_fac (U : C) (hU : good U) (i : I) :
      (c.ι.app i).app (op U) ≫ localDesc U hU = (r.ι.app i).app (op U) :=
    (Classical.choice hU).fac _ i
  have localDesc_natural := fun {U V : C} (f : U ⟶ V) (hV : good V) (hU : good U) =>
    localDesc_naturality_of_isColimit c r f (Classical.choice hV) (Classical.choice hU)
  have factorMap_eq {U V : C} (f : U ⟶ V)
      {T₁ T₂ : C} (hT₁ : good T₁) (hT₂ : good T₂)
      (k₁ : U ⟶ T₁) (g₁ : T₁ ⟶ V) (k₂ : U ⟶ T₂) (g₂ : T₂ ⟶ V)
      (hcomp : k₁ ≫ g₁ = k₂ ≫ g₂) :
      c.pt.map g₁.op ≫ localDesc T₁ hT₁ ≫ Y.obj.map k₁.op =
        c.pt.map g₂.op ≫ localDesc T₂ hT₂ ≫ Y.obj.map k₂.op := by
    obtain ⟨L, Z, q, hq, hgood⟩ := hEnough U
    have key {T V : C} (hT : good T) (k : U ⟶ T) (g : T ⟶ V) (j : L) :
        (c.pt.map g.op ≫ localDesc T hT ≫ Y.obj.map k.op) ≫ Y.obj.map (q j).op =
          c.pt.map ((q j ≫ k) ≫ g).op ≫ localDesc (Z j) (hgood j) := by
      have := localDesc_natural (q j ≫ k) hT (hgood j)
      simp only [op_comp, Functor.map_comp, Category.assoc] at this ⊢
      rw [← this]
    apply Y.property.hom_ext_ofArrows q hq
    intro j
    rw [key hT₁ k₁ g₁, key hT₂ k₂ g₂, Category.assoc, hcomp, ← Category.assoc]
  let R (V : C) : Presieve V := fun T _ => good T
  let S (V : C) : K.Cover V := by
    refine ⟨Sieve.generate (R V), ?_⟩
    obtain ⟨L, Z, f, hf, hgood⟩ := hEnough V
    exact K.superset_covering (Sieve.generate_mono fun _ _ ⟨i⟩ => hgood i) hf
  let family (V : C) (I₀ : (S V).Arrow) :
      c.pt.obj (op V) ⟶ Y.obj.obj (op I₀.Y) := by
    let domain := I₀.hf.choose
    let first := I₀.hf.choose_spec.choose
    let second := I₀.hf.choose_spec.choose_spec.choose
    exact c.pt.map second.op ≫ localDesc domain
      I₀.hf.choose_spec.choose_spec.choose_spec.1 ≫ Y.obj.map first.op
  have family_eq (V : C) (I₀ : (S V).Arrow) {T : C} (hT : good T)
      (k : I₀.Y ⟶ T) (g : T ⟶ V) (hkg : k ≫ g = I₀.f) :
      family V I₀ = c.pt.map g.op ≫ localDesc T hT ≫ Y.obj.map k.op :=
    factorMap_eq I₀.f _ hT _ _ k g
      (I₀.hf.choose_spec.choose_spec.choose_spec.2.trans hkg.symm)
  have family_compatible (V : C) :
      ∀ ⦃I₁ I₂ : (S V).Arrow⦄ (r₁₂ : I₁.Relation I₂),
        family V I₁ ≫ Y.obj.map r₁₂.g₁.op = family V I₂ ≫ Y.obj.map r₁₂.g₂.op := by
    intro I₁ I₂ r₁₂
    obtain ⟨T₁, k₁, g₁, hT₁, hk₁⟩ := I₁.hf
    obtain ⟨T₂, k₂, g₂, hT₂, hk₂⟩ := I₂.hf
    have hcomp : (r₁₂.g₁ ≫ k₁) ≫ g₁ = (r₁₂.g₂ ≫ k₂) ≫ g₂ := by
      simpa only [Category.assoc, hk₁, hk₂] using r₁₂.w
    rw [family_eq V I₁ hT₁ k₁ g₁ hk₁, family_eq V I₂ hT₂ k₂ g₂ hk₂]
    simpa [op_comp, Category.assoc] using
      factorMap_eq (r₁₂.g₁ ≫ I₁.f) hT₁ hT₂
        (r₁₂.g₁ ≫ k₁) g₁ (r₁₂.g₂ ≫ k₂) g₂ hcomp
  let descAt (V : C) : c.pt.obj (op V) ⟶ Y.obj.obj (op V) :=
    Y.property.amalgamate (S V) (family V) (family_compatible V)
  have descAt_map (V : C) (I₀ : (S V).Arrow) :
      descAt V ≫ Y.obj.map I₀.f.op = family V I₀ :=
    Y.property.amalgamate_map (S V) (family V) (family_compatible V) I₀
  let δ : c.pt ⟶ Y.obj := {
    app := fun V => descAt V.unop
    naturality := by
      intro U V f
      apply Y.property.hom_ext (S V.unop)
      intro I₀
      obtain ⟨T, k, g, hT, hkg⟩ := I₀.hf
      let I₁ : (S U.unop).Arrow :=
        ⟨I₀.Y, I₀.f ≫ f.unop, ⟨T, k, g ≫ f.unop, hT, by rw [← hkg]; simp⟩⟩
      calc
        (c.pt.map f ≫ descAt V.unop) ≫ Y.obj.map I₀.f.op =
            c.pt.map f ≫ family V.unop I₀ := by rw [Category.assoc, descAt_map]
        _ = family U.unop I₁ := by
            rw [family_eq V.unop I₀ hT k g hkg,
              family_eq U.unop I₁ hT k (g ≫ f.unop) (by
                dsimp [I₁]
                rw [← hkg, Category.assoc])]
            simp [op_comp, Category.assoc]
        _ = descAt U.unop ≫ Y.obj.map (I₀.f ≫ f.unop).op := (descAt_map U.unop I₁).symm
        _ = (descAt U.unop ≫ Y.obj.map f) ≫ Y.obj.map I₀.f.op := by
            simp [op_comp, Category.assoc]
  }
  have δ_fac (i : I) : c.ι.app i ≫ δ = η i := by
    ext U
    apply Y.property.hom_ext (S U.unop)
    intro I₀
    obtain ⟨T, k, g, hT, hkg⟩ := I₀.hf
    show ((c.ι.app i).app U ≫ descAt U.unop) ≫ Y.obj.map I₀.f.op =
      (η i).app U ≫ Y.obj.map I₀.f.op
    rw [Category.assoc, descAt_map, family_eq U.unop I₀ hT k g hkg]
    calc
      (c.ι.app i).app U ≫ c.pt.map g.op ≫ localDesc T hT ≫ Y.obj.map k.op =
          (F.obj i).map g.op ≫ (c.ι.app i).app (op T) ≫ localDesc T hT ≫
            Y.obj.map k.op := by
              simpa only [Category.assoc, Functor.const_obj_obj, op_unop] using congrArg
                (fun morphism => morphism ≫ localDesc T hT ≫ Y.obj.map k.op)
                ((c.ι.app i).naturality g.op).symm
      _ = (F.obj i).map g.op ≫ (r.ι.app i).app (op T) ≫ Y.obj.map k.op := by
            simpa only [Category.assoc] using congrArg
              (fun morphism => (F.obj i).map g.op ≫ morphism ≫ Y.obj.map k.op)
              (localDesc_fac T hT i)
      _ = (r.ι.app i).app U ≫ Y.obj.map (k ≫ g).op := by
            simpa only [op_comp, Y.obj.map_comp, Category.assoc, op_unop,
              Functor.const_obj_obj, r] using congrArg
              (fun morphism => morphism ≫ Y.obj.map k.op)
              ((r.ι.app i).naturality g.op)
      _ = (r.ι.app i).app U ≫ Y.obj.map I₀.f.op := by rw [hkg]
  refine ⟨δ, δ_fac, ?_⟩
  intro δ' hδ'
  apply NatTrans.ext
  funext V
  show δ'.app V = descAt V.unop
  apply Y.property.hom_ext (S V.unop)
  intro I₀
  obtain ⟨T, k, g, hT, hkg⟩ := I₀.hf
  rw [descAt_map, family_eq V.unop I₀ hT k g hkg]
  have hdesc : δ'.app (op T) = localDesc T hT := by
    apply (Classical.choice hT).hom_ext
    intro i
    have hfac :
        (c.ι.app i).app (op T) ≫ δ'.app (op T) = (r.ι.app i).app (op T) := by
      simpa using congrArg (fun η : F.obj i ⟶ Y.obj => (η.app (op T))) (hδ' i)
    exact hfac.trans (localDesc_fac T hT i).symm
  rw [← hkg, op_comp, Y.obj.map_comp, ← Category.assoc,
    ← δ'.naturality g.op, hdesc]
  exact Category.assoc _ _ _

/-- **Sheafification carries an objectwise colimit over enough objects to a colimit.** A cocone
of presheaves which becomes a colimit cocone after evaluation at the members of a covering family
of every object of the site is carried by sheafification to a colimit cocone of sheaves. -/
noncomputable def isColimit_presheafToSheaf_mapCocone_of_hasEnoughObjects
    (K : GrothendieckTopology C) [HasSheafify K A] (c : Cocone F)
    (hEnough : K.HasEnoughObjects
      (fun U => Nonempty (IsColimit (((evaluation Cᵒᵖ A).obj (op U)).mapCocone c)))) :
    IsColimit ((presheafToSheaf K A).mapCocone c) := by
  classical
  let adj := sheafificationAdjunction K A
  let η (s : Cocone (F ⋙ presheafToSheaf K A)) (i : I) :
      F.obj i ⟶ (sheafToPresheaf K A).obj s.pt :=
    adj.homEquiv (F.obj i) s.pt (s.ι.app i)
  have hη (s : Cocone (F ⋙ presheafToSheaf K A)) {i j : I} (f : i ⟶ j) :
      F.map f ≫ η s j = η s i := by
    dsimp [η]
    calc
      F.map f ≫ adj.homEquiv (F.obj j) s.pt (s.ι.app j) =
          adj.homEquiv (F.obj i) s.pt
            ((presheafToSheaf K A).map (F.map f) ≫ s.ι.app j) := by
              symm
              exact adj.homEquiv_naturality_left (F.map f) (s.ι.app j)
      _ = adj.homEquiv (F.obj i) s.pt (s.ι.app i) := by
            exact congrArg (adj.homEquiv (F.obj i) s.pt) (s.w f)
  let desc0 (s : Cocone (F ⋙ presheafToSheaf K A)) : c.pt ⟶ s.pt.obj :=
    Classical.choose
      (existsUnique_presheafCoconeDesc_of_hasEnoughObjects K c s.pt (η s) (hη s) hEnough)
  have hdesc0 (s : Cocone (F ⋙ presheafToSheaf K A)) (i : I) :
      c.ι.app i ≫ desc0 s = η s i :=
    (Classical.choose_spec
      (existsUnique_presheafCoconeDesc_of_hasEnoughObjects K c s.pt (η s) (hη s) hEnough)).1 i
  refine IsColimit.mk (fun s => (adj.homEquiv c.pt s.pt).symm (desc0 s)) ?_ ?_
  · intro s i
    apply (adj.homEquiv (F.obj i) s.pt).injective
    change adj.homEquiv (F.obj i) s.pt
      ((presheafToSheaf K A).map (c.ι.app i) ≫
        (adj.homEquiv c.pt s.pt).symm (desc0 s)) = η s i
    rw [adj.homEquiv_naturality_left]
    change c.ι.app i ≫ (adj.homEquiv c.pt s.pt)
      ((adj.homEquiv c.pt s.pt).symm (desc0 s)) = η s i
    rw [Equiv.apply_symm_apply]
    exact hdesc0 s i
  · intro s m hm
    apply (adj.homEquiv c.pt s.pt).injective
    rw [Equiv.apply_symm_apply]
    apply (Classical.choose_spec
      (existsUnique_presheafCoconeDesc_of_hasEnoughObjects K c s.pt (η s) (hη s) hEnough)).2
    intro i
    calc
      c.ι.app i ≫ adj.homEquiv c.pt s.pt m =
          adj.homEquiv (F.obj i) s.pt
            ((presheafToSheaf K A).map (c.ι.app i) ≫ m) :=
        (adj.homEquiv_naturality_left (c.ι.app i) m).symm
      _ = η s i := congrArg (adj.homEquiv (F.obj i) s.pt) (hm i)

end Sheafification

section HigherDirectImage

open Stacks.Cohomology.SheafifiedHigherDirectImage

variable {C : Type a} [Category.{a'} C] {D : Type d} [Category.{d'} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type b) [Category.{b'} A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  [EnoughInjectives (Sheaf K A)] (u : D ⥤ C) [u.IsContinuous J K]

/-- **The local criterion of Stacks 0H7B on a locally small site.** Let `u : 𝒟 ⥤ 𝒞` be a
continuous functor of sites and let `F` be a diagram of sheaves on `𝒞` with values in an abelian
category. If every object of `𝒟` has a covering `{V_i → V}` such that each `H^p(u(V_i), -)`
preserves the colimit of `F`, then the higher direct image `R^p f_*` preserves the colimit of
`F`. -/
theorem preservesColimit_rightDerived_sheafPushforwardContinuous_of_hasEnoughObjects
    (p : ℕ) {I : Type c} [Category.{c'} I] (F : I ⥤ Sheaf K A)
    (h : J.HasEnoughObjects (fun V => PreservesColimit F
      (((sheafSections K A).obj (op (u.obj V))).rightDerived p))) :
    PreservesColimit F ((u.sheafPushforwardContinuous A J K).rightDerived p) := by
  refine ⟨fun {c} hc => ?_⟩
  let a := presheafToSheaf J A
  let H := (pushforwardCohomologyPresheaf (K := K) A u).rightDerived p
  have hEnough : J.HasEnoughObjects
      (fun V => Nonempty (IsColimit
        (((evaluation Dᵒᵖ A).obj (op V)).mapCocone (H.mapCocone c)))) := by
    intro V
    obtain ⟨L, Z, q, hq, hgood⟩ := h V
    refine ⟨L, Z, q, hq, fun i => ?_⟩
    let eval := (evaluation Dᵒᵖ A).obj (op (Z i))
    have : PreservesColimit F
        ((pushforwardCohomologyPresheaf (K := K) A u ⋙ eval).rightDerived p) := hgood i
    have : PreservesColimit F (H ⋙ eval) :=
      preservesColimit_of_natIso F (pushforwardCohomologyPresheafEvaluationIso A u p (Z i))
    exact ⟨isColimitOfPreserves (H ⋙ eval) hc⟩
  have hcolim : IsColimit ((H ⋙ a).mapCocone c) :=
    isColimit_presheafToSheaf_mapCocone_of_hasEnoughObjects J (H.mapCocone c) hEnough
  have : PreservesColimit F (H ⋙ a) := preservesColimit_of_preserves_colimit_cocone hc hcolim
  have : PreservesColimit F ((u.sheafPushforwardContinuous A J K).rightDerived p) :=
    preservesColimit_of_natIso F (rightDerivedPushforwardIso A u p).symm
  exact ⟨isColimitOfPreserves _ hc⟩

end HigherDirectImage

end Stacks.Cohomology.HigherDirectImage
