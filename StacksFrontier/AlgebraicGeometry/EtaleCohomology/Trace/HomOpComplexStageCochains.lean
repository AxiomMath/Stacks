module

public import Mathlib.Algebra.Module.ZMod
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InjectiveSheafSections
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexQuasiIso

/-!
# Sections of the internal Hom complex over an étale `X`-scheme are Hom cochains

Let `X` be a scheme, `W` an étale `X`-scheme, `Λ` a ring with a ring map `ℤ/n ⟶ Λ`, `L` a complex
of sheaves of `Λ`-modules and `K` a complex of sheaves of `ℤ/n`-modules on `X_étale`, with
underlying complex of abelian sheaves `M`. A section over `W` of the internal Hom complex
`ℋom^•_ℤ(L, M)` (`Stacks.AbelianInternalHom.homOpComplex`) is a family of morphisms of abelian
sheaves `L^p|_W ⟶ M^q|_W`; these are automatically `ℤ/n`-linear, so it is a cochain of degree
`m` of the Hom complex `Hom^•(L|_W, K|_W)` in the abelian category of sheaves of `ℤ/n`-modules on
`W_étale`. This file builds that identification degreewise, as an additive bijection
(`Stacks.EtaleCohomology.stageCochain`, `Stacks.EtaleCohomology.bijective_stageCochain`); its
compatibility with the differentials and with precomposition, and the resulting statement on
cohomology, are in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/HomOpComplexStageQuasiIso.lean`.

## Main definitions

* `Stacks.EtaleCohomology.overEtaleEquivalence`: `Over W ≌ W_étale` for `W : X.Etale`.
* `Stacks.EtaleCohomology.stageSectionHom`: a section of `ℋom_ℤ(G, F)` over `W` as a morphism
  `G|_W ⟶ F|_W` of sheaves of `ℤ/n`-modules on `W_étale` (bijective:
  `Stacks.EtaleCohomology.stageSectionHom_injective`,
  `Stacks.EtaleCohomology.stageSectionHom_surjective`).
* `Stacks.EtaleCohomology.stageSectionHomPQ`: the same on the factor `ℋom_ℤ(L^p, M^q)`.
* `Stacks.EtaleCohomology.stageCochain`: a section of `ℋom^m_ℤ(L, M)` over `W` as a degree-`m`
  cochain `L|_W ⟶ K|_W`.

## Implementation notes

The complexes `L` and `M` are spelled in the coefficient universe `max (u + 1) u` in which
`Stacks.AbelianInternalHom.homOpComplex` takes them on `X_étale`, and the factors are indexed by
`Stacks.AbelianInternalHom.HomOpIndex` exactly as in `homOpComplexπ`: the kernel checks equality
of the carrier types of sections of these sheaves by unfolding them, which is very slow unless
the two sheaf expressions are syntactically equal.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-! ### `Over W` is the small étale site of `W` -/

section OverEtale

variable {X : Scheme.{u}} (W : X.Etale)

/-- An étale `X`-scheme over `W` as an étale `W`-scheme. -/
def overEtaleFunctor : Over W ⥤ W.left.Etale where
  obj V := MorphismProperty.Over.mk ⊤ V.hom.left inferInstance
  map g := MorphismProperty.Over.homMk g.left.left (congrArg (fun m ↦ m.left) g.w)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An étale `W`-scheme `V`, as the étale `X`-scheme `V ⟶ W ⟶ X` over `W`. Composed with
`Over.forget W` it is `Scheme.Etale.smallEtaleCompose W.hom`. -/
def overEtaleInverse : W.left.Etale ⥤ Over W where
  obj V := Over.mk (X := W) (Y := (Scheme.Etale.smallEtaleCompose W.hom).obj V)
    (MorphismProperty.Over.homMk V.hom rfl)
  map {V V'} g := Over.homMk ((Scheme.Etale.smallEtaleCompose W.hom).map g) (by
    apply MorphismProperty.Over.Hom.ext
    change g.left ≫ V'.hom = V.hom
    exact MorphismProperty.Over.w g)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **`Over W` is equivalent to the small étale site of `W`**, for `W` étale over `X`. -/
def overEtaleEquivalence : Over W ≌ W.left.Etale where
  functor := overEtaleFunctor W
  inverse := overEtaleInverse W
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (V.hom.left ≫ W.hom) = V.left.hom
      simp)) (by
        apply MorphismProperty.Comma.Hom.ext
        · change 𝟙 _ ≫ V.hom.left = V.hom.left
          simp
        · apply Subsingleton.elim)) (by
          intro V V' g
          apply Over.OverMorphism.ext
          apply MorphismProperty.Comma.Hom.ext
          · change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
            simp
          · apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)) (by
      intro V V' g
      apply MorphismProperty.Comma.Hom.ext
      · change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
        simp
      · apply Subsingleton.elim)

/-- Restricting a morphism of presheaves on `Over W` to the small étale site of `W` is
bijective. -/
lemma bijective_whiskerLeft_overEtaleInverse {D : Type*} [Category* D]
    (P Q : (Over W)ᵒᵖ ⥤ D) :
    Function.Bijective (fun s : P ⟶ Q ↦ Functor.whiskerLeft (overEtaleInverse W).op s) :=
  ((overEtaleEquivalence W).op.congrLeft (E := D)).fullyFaithfulFunctor.map_bijective P Q

end OverEtale

/-! ### A section of `ℋom_ℤ(G, F)` over `W` as a morphism of sheaves on `W_étale` -/

section Component

variable {X : Scheme.{u}} (W : X.Etale) {Λ : Type} [Ring Λ] {n : ℕ} (ψ : ZMod n →+* Λ)

/-- The abelian sheaf underlying a sheaf of `ℤ/n`-modules on `X_étale`. -/
abbrev zmodToAb (F : EtaleModules.{u, 0} (ZMod n) X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Stacks.AbelianInternalHom.toAb X.smallEtaleTopology F

/-- Restriction to `W_étale`, after restricting scalars to `ℤ/n`. -/
abbrev stageRestrict : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} (ZMod n) W.left :=
  etaleModuleRestrictScalars ψ X ⋙ etaleModuleRestriction.{u, 0} (ZMod n) W.hom

/-- A section over `W` of `ℋom_ℤ(G, F)`, as a natural transformation over `Over W`. -/
abbrev homOpSectionNatTrans (G : EtaleModules.{u, 0} Λ X) (F : EtaleModules.{u, 0} (ZMod n) X)
    (s : (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj
      (op W)) :
    (Over.forget W).op ⋙ (Stacks.AbelianInternalHom.toAb X.smallEtaleTopology G).obj ⟶
      (Over.forget W).op ⋙ (zmodToAb F).obj :=
  s

/-- **A section of `ℋom_ℤ(G, F)` over `W` as a morphism `G|_W ⟶ F|_W`** of sheaves of
`ℤ/n`-modules on `W_étale`: its components are those of the section over the étale
`X`-schemes `V ⟶ W ⟶ X`, which are `ℤ/n`-linear because they are additive. -/
def stageSectionHom (G : EtaleModules.{u, 0} Λ X) (F : EtaleModules.{u, 0} (ZMod n) X)
    (s : (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj
      (op W)) :
    (stageRestrict W ψ).obj G ⟶ (etaleModuleRestriction.{u, 0} (ZMod n) W.hom).obj F :=
  ObjectProperty.homMk
    { app V := ModuleCat.ofHom (X := ((stageRestrict W ψ).obj G).obj.obj V)
        (Y := ((etaleModuleRestriction.{u, 0} (ZMod n) W.hom).obj F).obj.obj V)
        (AddMonoidHom.toZModLinearMap n
          ((homOpSectionNatTrans W G F s).app (op ((overEtaleInverse W).obj V.unop))).hom)
      naturality V V' a := by
        ext x
        exact ConcreteCategory.congr_hom
          ((homOpSectionNatTrans W G F s).naturality ((overEtaleInverse W).map a.unop).op) x }

/-- The components of `stageSectionHom s` on sections are those of the section `s` over the étale
`X`-schemes `V ⟶ W ⟶ X`. -/
lemma stageSectionHom_app_apply (G : EtaleModules.{u, 0} Λ X)
    (F : EtaleModules.{u, 0} (ZMod n) X)
    (s : (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj
      (op W)) (V : W.left.Etaleᵒᵖ) (x : ((stageRestrict W ψ).obj G).obj.obj V) :
    ((stageSectionHom W ψ G F s).hom.app V).hom x =
      ((homOpSectionNatTrans W G F s).app (op ((overEtaleInverse W).obj V.unop))).hom x :=
  rfl

/-- Morphisms of sheaves of `ℤ/n`-modules are equal when they agree on all sections. -/
private lemma hom_ext_of_apply_eq {Y : Scheme.{u}} {A B : EtaleModules.{u, 0} (ZMod n) Y}
    {f g : A ⟶ B} (h : ∀ V x, (f.hom.app V).hom x = (g.hom.app V).hom x) : f = g :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ModuleCat.hom_ext
    (LinearMap.ext fun x => h V x)))

/-- A section of `ℋom_ℤ(G, F)` over `W` is determined by the morphism `stageSectionHom s`. -/
lemma stageSectionHom_injective (G : EtaleModules.{u, 0} Λ X)
    (F : EtaleModules.{u, 0} (ZMod n) X) :
    Function.Injective (stageSectionHom W ψ G F) := by
  intro s t h
  apply (bijective_whiskerLeft_overEtaleInverse W _ _).1
  refine NatTrans.ext (funext fun V => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_))
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun φ : (stageRestrict W ψ).obj G ⟶ _ => φ.hom) h) V) x

/-- Each morphism `G|_W ⟶ F|_W` of sheaves of `ℤ/n`-modules on `W_étale` is `stageSectionHom s`
for a section `s` of `ℋom_ℤ(G, F)` over `W`. -/
lemma stageSectionHom_surjective (G : EtaleModules.{u, 0} Λ X)
    (F : EtaleModules.{u, 0} (ZMod n) X) :
    Function.Surjective (stageSectionHom W ψ G F) := by
  intro g
  let w : (overEtaleInverse W).op ⋙ (Over.forget W).op ⋙
        (Stacks.AbelianInternalHom.toAb X.smallEtaleTopology G).obj ⟶
      (overEtaleInverse W).op ⋙ (Over.forget W).op ⋙ (zmodToAb F).obj :=
    { app V := AddCommGrpCat.ofHom (g.hom.app V).hom.toAddMonoidHom
      naturality V V' a := by
        ext x
        exact ConcreteCategory.congr_hom (g.hom.naturality a) x }
  obtain ⟨s, hs⟩ := (bijective_whiskerLeft_overEtaleInverse W _ _).2 w
  exact ⟨s, hom_ext_of_apply_eq fun V x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app hs V) x⟩

/-- `stageSectionHom` takes a sum of sections to the sum of the corresponding morphisms. -/
lemma stageSectionHom_add (G : EtaleModules.{u, 0} Λ X) (F : EtaleModules.{u, 0} (ZMod n) X)
    (s t : (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj
      (op W)) :
    stageSectionHom W ψ G F (s + t) = stageSectionHom W ψ G F s + stageSectionHom W ψ G F t :=
  hom_ext_of_apply_eq fun _ _ => rfl

/-- **Postcomposition**: the section `s ≫ g` corresponds to `stageSectionHom s ≫ g|_W`. -/
lemma stageSectionHom_homOpMap (G : EtaleModules.{u, 0} Λ X)
    {F F' : EtaleModules.{u, 0} (ZMod n) X} (g : F ⟶ F')
    (s : (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj
      (op W)) :
    stageSectionHom W ψ G F' ((Stacks.AbelianInternalHom.homOpMap X.smallEtaleTopology G
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).map g)).hom.app
          (op W) s) =
      stageSectionHom W ψ G F s ≫ (etaleModuleRestriction.{u, 0} (ZMod n) W.hom).map g :=
  hom_ext_of_apply_eq fun _ _ => rfl

/-- **Precomposition**: the section `v ≫ s` corresponds to `v|_W ≫ stageSectionHom s`. -/
lemma stageSectionHom_homOpMapLeft {G G' : EtaleModules.{u, 0} Λ X} (v : G' ⟶ G)
    (F : EtaleModules.{u, 0} (ZMod n) X)
    (s : (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj
      (op W)) :
    stageSectionHom W ψ G' F ((Stacks.AbelianInternalHom.homOpMapLeft X.smallEtaleTopology v
        (zmodToAb F)).hom.app (op W) s) =
      (stageRestrict W ψ).map v ≫ stageSectionHom W ψ G F s :=
  hom_ext_of_apply_eq fun _ _ => rfl

/-- `stageSectionHom` as an additive map. -/
def stageSectionHomAddHom (G : EtaleModules.{u, 0} Λ X) (F : EtaleModules.{u, 0} (ZMod n) X) :
    (Stacks.AbelianInternalHom.homOpSheaf X.smallEtaleTopology G (zmodToAb F)).obj.obj (op W) →+
      ((stageRestrict W ψ).obj G ⟶ (etaleModuleRestriction.{u, 0} (ZMod n) W.hom).obj F) where
  toFun := stageSectionHom W ψ G F
  map_zero' := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => ModuleCat.hom_ext
    (LinearMap.ext fun _ => rfl)))
  map_add' := stageSectionHom_add W ψ G F

end Component

/-! ### Sections of the internal Hom complex over `W` as cochains -/

section Cochains

open CochainComplex.HomComplex Stacks.AbelianInternalHom

attribute [local instance] moduleCat_hasLimitsOfSize

variable {X : Scheme.{u}} (W : X.Etale) {Λ : Type} [Ring Λ] {n : ℕ} (ψ : ZMod n →+* Λ)

/-- The complex of abelian sheaves underlying a complex of sheaves of `ℤ/n`-modules, in the
coefficient universe `max (u + 1) u` in which `Stacks.AbelianInternalHom.homOpComplex` takes its
arguments on `X_étale`. -/
abbrev zmodForgetComplex (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) X) ℤ) :
    CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) u}) ℤ :=
  ((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{max (u + 1) u} (ZMod n))
    AddCommGrpCat.{max (u + 1) u})).mapHomologicalComplex _).obj K

variable (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ)
  (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) X) ℤ)

/-- The restriction of `L` to `W_étale`, as a complex of sheaves of `ℤ/n`-modules. -/
abbrev stageComplex : CochainComplex (EtaleModules.{u, 0} (ZMod n) W.left) ℤ :=
  ((stageRestrict W ψ).mapHomologicalComplex _).obj L

/-- The restriction of `K` to `W_étale`. -/
abbrev stageZModComplex : CochainComplex (EtaleModules.{u, 0} (ZMod n) W.left) ℤ :=
  ((etaleModuleRestriction.{u, 0} (ZMod n) W.hom).mapHomologicalComplex _).obj K

/-- `Stacks.EtaleCohomology.stageSectionHom` on the factor `ℋom_ℤ(L^p, M^q)` of the internal Hom
complex, `M` the complex underlying `K`: a section over `W` as a morphism `L^p|_W ⟶ K^q|_W`. -/
def stageSectionHomPQ (p q : ℤ) :
    (homOpSheaf X.smallEtaleTopology (L.X p) ((zmodForgetComplex K).X q)).obj.obj (op W) →+
      ((stageComplex W ψ L).X p ⟶ (stageZModComplex W K).X q) :=
  stageSectionHomAddHom W ψ (L.X p) (K.X q)

/-- Sections over `W` of `ℋom_ℤ(L^p, M^q)` correspond bijectively, via `stageSectionHomPQ`, to
morphisms `L^p|_W ⟶ K^q|_W`. -/
lemma bijective_stageSectionHomPQ (p q : ℤ) :
    Function.Bijective (stageSectionHomPQ W ψ L K p q) :=
  ⟨stageSectionHom_injective W ψ (L.X p) (K.X q), stageSectionHom_surjective W ψ (L.X p) (K.X q)⟩

/-- Postcomposition with the differential of `M` is postcomposition with that of `K|_W`. -/
lemma stageSectionHomPQ_homOpMap (p : ℤ) {q q' : ℤ}
    (t : (homOpSheaf X.smallEtaleTopology (L.X p) ((zmodForgetComplex K).X q)).obj.obj (op W)) :
    stageSectionHomPQ W ψ L K p q' ((homOpMap X.smallEtaleTopology (L.X p)
        ((zmodForgetComplex K).d q q')).hom.app (op W) t) =
      stageSectionHomPQ W ψ L K p q t ≫ (stageZModComplex W K).d q q' :=
  stageSectionHom_homOpMap W ψ (L.X p) (K.d q q') t

/-- Precomposition with the differential of `L` is precomposition with that of `L|_W`. -/
lemma stageSectionHomPQ_homOpMapLeft_d {p p' : ℤ} (q : ℤ)
    (t : (homOpSheaf X.smallEtaleTopology (L.X p') ((zmodForgetComplex K).X q)).obj.obj (op W)) :
    stageSectionHomPQ W ψ L K p q ((homOpMapLeft X.smallEtaleTopology (L.d p p')
        ((zmodForgetComplex K).X q)).hom.app (op W) t) =
      (stageComplex W ψ L).d p p' ≫ stageSectionHomPQ W ψ L K p' q t :=
  stageSectionHom_homOpMapLeft W ψ (L.d p p') (K.X q) t

/-- Precomposition with a morphism of complexes `f : L' ⟶ L` is precomposition with `f|_W`. -/
lemma stageSectionHomPQ_homOpMapLeft_f
    {L' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ}
    (f : L' ⟶ L) (p q : ℤ)
    (t : (homOpSheaf X.smallEtaleTopology (L.X p) ((zmodForgetComplex K).X q)).obj.obj (op W)) :
    stageSectionHomPQ W ψ L' K p q ((homOpMapLeft X.smallEtaleTopology (f.f p)
        ((zmodForgetComplex K).X q)).hom.app (op W) t) =
      (((stageRestrict W ψ).mapHomologicalComplex _).map f).f p ≫
        stageSectionHomPQ W ψ L K p q t :=
  stageSectionHom_homOpMapLeft W ψ (f.f p) (K.X q) t

/-- The section over `W` of the factor `ℋom_ℤ(L^p, M^q)` of a section of `ℋom^m_ℤ(L, M)`. -/
abbrev homOpComplexStageπ {m : ℤ} (x : HomOpIndex m)
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :=
  ((homOpComplexπ X.smallEtaleTopology L (zmodForgetComplex K) m x).hom.app (op W)).hom s

/-- **Sections over `W` of `ℋom^m_ℤ(L, M)` are the families of sections of its factors.** -/
lemma bijective_homOpComplexStageπ (m : ℤ) :
    Function.Bijective (fun (s : (homOpComplexX X.smallEtaleTopology L
        (zmodForgetComplex K) m).obj.obj (op W)) (x : HomOpIndex m) =>
      homOpComplexStageπ W L K x s) := by
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)).obj (op W)
  let f := fun x : HomOpIndex m =>
    homOpSheaf X.smallEtaleTopology (L.X x.1.1) ((zmodForgetComplex K).X x.1.2)
  have : PreservesLimit (Discrete.functor f) E :=
    preservesLimit_of_natIso _
      (sheafSectionsNatIsoEvaluation X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)
        (X := W)).symm
  let e := piComparison E f ≫
    (ModuleCat.piIsoPi.{0, 0, max (u + 1) u} (fun x => E.obj (f x))).hom
  have hb : Function.Bijective e := ConcreteCategory.bijective_of_isIso e
  have key : ∀ (s : E.obj (∏ᶜ f)) (x : HomOpIndex m),
      (e s : ∀ x, E.obj (f x)) x = (E.map (Pi.π f x)) s := by
    intro s x
    have h1 := ModuleCat.piIsoPi_hom_ker_subtype_apply.{0, 0, max (u + 1) u}
      (fun x => E.obj (f x)) x ((piComparison E f) s)
    simp only at h1
    change ((ModuleCat.piIsoPi.{0, 0, max (u + 1) u} (fun x => E.obj (f x))).hom
      ((piComparison E f) s)) x = _
    rw [h1, ← ConcreteCategory.comp_apply, piComparison_comp_π]
  refine ⟨fun s t h => hb.1 (funext fun x => (key s x).trans ((congrFun h x).trans
    (key t x).symm)), fun t => ?_⟩
  obtain ⟨s, hs⟩ := hb.2 t
  exact ⟨s, funext fun x => (key s x).symm.trans (congrFun hs x)⟩

/-- **A section of `ℋom^m_ℤ(L, M)` over `W` as a degree-`m` cochain `L|_W ⟶ K|_W`** of
complexes of sheaves of `ℤ/n`-modules on `W_étale`. -/
def stageCochain (m : ℤ) :
    (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W) →+
      Cochain (stageComplex W ψ L) (stageZModComplex W K) m where
  toFun s := Cochain.mk fun p q hpq =>
    stageSectionHomPQ W ψ L K (⟨(p, q), hpq⟩ : HomOpIndex m).1.1
      (⟨(p, q), hpq⟩ : HomOpIndex m).1.2 (homOpComplexStageπ W L K ⟨(p, q), hpq⟩ s)
  map_zero' := Cochain.ext _ _ fun p q hpq => by
    have h0 : homOpComplexStageπ W L K ⟨(p, q), hpq⟩ 0 = 0 := map_zero _
    rw [Cochain.mk_v, Cochain.zero_v, h0, map_zero]
  map_add' s t := Cochain.ext _ _ fun p q hpq => by
    have h0 : homOpComplexStageπ W L K ⟨(p, q), hpq⟩ (s + t) =
        homOpComplexStageπ W L K ⟨(p, q), hpq⟩ s + homOpComplexStageπ W L K ⟨(p, q), hpq⟩ t :=
      map_add _ _ _
    rw [Cochain.mk_v, Cochain.add_v, Cochain.mk_v, Cochain.mk_v, h0, map_add]

/-- The component of the cochain `stageCochain s` in degrees `(p, q)` is `stageSectionHomPQ`
applied to the factor of `s` in `ℋom_ℤ(L^p, M^q)`. -/
lemma stageCochain_v (m : ℤ)
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W))
    (p q : ℤ) (hpq : p + m = q) :
    (stageCochain W ψ L K m s).v p q hpq =
      stageSectionHomPQ W ψ L K (⟨(p, q), hpq⟩ : HomOpIndex m).1.1
        (⟨(p, q), hpq⟩ : HomOpIndex m).1.2 (homOpComplexStageπ W L K ⟨(p, q), hpq⟩ s) :=
  rfl

/-- **Sections over `W` of `ℋom^m_ℤ(L, M)` are the degree-`m` cochains `L|_W ⟶ K|_W`**:
the map `stageCochain` is bijective. -/
lemma bijective_stageCochain (m : ℤ) : Function.Bijective (stageCochain W ψ L K m) := by
  refine ⟨fun s t h => (bijective_homOpComplexStageπ W L K m).1 (funext fun x => ?_),
    fun z => ?_⟩
  · obtain ⟨⟨p, q⟩, hpq⟩ := x
    refine (bijective_stageSectionHomPQ W ψ L K _ _).1 ?_
    exact congrArg (fun c : Cochain _ _ m => c.v p q hpq) h
  · choose t ht using fun x : HomOpIndex m =>
      (bijective_stageSectionHomPQ W ψ L K x.1.1 x.1.2).2 (z.v x.1.1 x.1.2 x.2)
    obtain ⟨s, hs⟩ := (bijective_homOpComplexStageπ W L K m).2 t
    refine ⟨s, Cochain.ext _ _ fun p q hpq => ?_⟩
    rw [stageCochain_v]
    exact (congrArg (stageSectionHomPQ W ψ L K _ _) (congrFun hs ⟨(p, q), hpq⟩)).trans
      (ht ⟨(p, q), hpq⟩)

end Cochains

end Stacks.EtaleCohomology
