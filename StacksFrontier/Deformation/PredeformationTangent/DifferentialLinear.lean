module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# Linearity of the differential of a morphism of predeformation categories

The differential of a morphism of predeformation categories is linear over the residue field
when the associated functors of isomorphism classes satisfy Schlessinger's condition (S2).

## Main results

* `Deformation.differential_isLinearMap`: linearity for the canonical tangent-space vector
  structures.

## Implementation notes

The canonical vector-space structures are those of Tag 06IH, packaged as instances under the
predeformation and (S2) hypotheses. The differential is the underlying function defined in Tag
06II. The source and target total categories may live in different universes.

Linearity is pulled back from the module-valued lifts: a family of maps between the values of
two linear functors on finitely generated modules which is natural in the module is linear at
the rank-one module, because addition and scalar multiplication are themselves induced by
morphisms of modules.

## References

* [Stacks Project, Tag 06IJ](https://stacks.math.columbia.edu/tag/06IJ)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A natural family of maps between the values of two linear functors on finitely generated
modules is linear at the rank-one module. -/
theorem isLinearMap_of_natural_on_fgModules
    (R : Type u) [CommRing R]
    (F : FGModuleCat.{u} R ⥤ ModuleCat.{v₁} R)
    (G : FGModuleCat.{u} R ⥤ ModuleCat.{v₂} R)
    [F.Additive] [G.Additive] [F.Linear R] [G.Linear R]
    (t : ∀ X, F.obj X → G.obj X)
    (ht : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X),
      t Y ((F.map f) x) = (G.map f) (t X x)) :
    IsLinearMap R (t (FGModuleCat.of R R)) := by
  let A : FGModuleCat.{u} R := FGModuleCat.of R R
  let B : FGModuleCat.{u} R := prodFGModule R A A
  let p₁ : B ⟶ A := prodFst R A A
  let p₂ : B ⟶ A := prodSnd R A A
  let i₁ : A ⟶ B := FGModuleCat.ofHom (LinearMap.inl R R R)
  let i₂ : A ⟶ B := FGModuleCat.ofHom (LinearMap.inr R R R)
  let add : B ⟶ A := FGModuleCat.ofHom (LinearMap.fst R R R + LinearMap.snd R R R)
  have hp₁i₁ : i₁ ≫ p₁ = 𝟙 A := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hp₂i₂ : i₂ ≫ p₂ = 𝟙 A := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hp₁i₂ : i₂ ≫ p₁ = 0 := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hp₂i₁ : i₁ ≫ p₂ = 0 := FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have hadd : add = p₁ + p₂ := FGModuleCat.hom_ext rfl
  refine ⟨fun x y => ?_, fun r x => ?_⟩
  · let z : F.obj B := (F.map i₁) x + (F.map i₂) y
    have hF : ∀ {f : A ⟶ B} {g : B ⟶ A} {e : A ⟶ A}, f ≫ g = e → ∀ w : F.obj A,
        (F.map g) ((F.map f) w) = (F.map e) w := by
      rintro f g e rfl w
      simp
    have h11 : (F.map p₁) ((F.map i₁) x) = x := (hF hp₁i₁ x).trans (by simp)
    have h12 : (F.map p₁) ((F.map i₂) y) = 0 := (hF hp₁i₂ y).trans (by simp)
    have h21 : (F.map p₂) ((F.map i₁) x) = 0 := (hF hp₂i₁ x).trans (by simp)
    have h22 : (F.map p₂) ((F.map i₂) y) = y := (hF hp₂i₂ y).trans (by simp)
    calc
      _ = t A ((F.map add) z) := by
        rw [hadd, F.map_add]
        simp [A, z, h11, h12, h21, h22]
      _ = (G.map add) (t B z) := ht add z
      _ = (G.map p₁) (t B z) + (G.map p₂) (t B z) := by rw [hadd, G.map_add]; rfl
      _ = t A x + t A y := by
        rw [← ht p₁ z, ← ht p₂ z]
        simp [z, h11, h12, h21, h22]
  · let f : A ⟶ A := r • (𝟙 A)
    calc
      _ = t A ((F.map f) x) := by simp [A, f]
      _ = (G.map f) (t A x) := ht f x
      _ = _ := by simp [A, f]

/-- Transporting along an equality of underlying functors commutes with the functorial
action. -/
theorem moduleFunctor_map_cast
    (R : Type u) [CommRing R] {C : Type v₁} [Category C]
    (F : C ⥤ ModuleCat.{v₂} R) (U : C ⥤ Type v₂)
    (h : F ⋙ forget (ModuleCat R) = U) {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    cast (congrArg (fun H : C ⥤ Type v₂ => H.obj Y) h) ((F.map f) x) =
      U.map f (cast (congrArg (fun H : C ⥤ Type v₂ => H.obj X) h) x) := by
  cases h
  rfl

/-- Casting along `h.symm` and then along `h` is the identity. -/
theorem cast_symm_cancel {α β : Type u} (h : α = β) (x : β) : cast h (cast h.symm x) = x := by
  cases h
  rfl

/-- Additive and scalar structures on a fixed carrier, used to transport them along an
equality of carriers. -/
abbrev AddModuleData (R : Type u) [CommRing R] (α : Type v₁) :=
  Σ G : AddCommGroup α, letI := G; Module R α

/-- Casting along `h` is additive for the structure on `α` and its transport to `β`. -/
theorem cast_add_rec {R : Type u} [CommRing R] {α β : Type v₁} (h : α = β)
    (D : AddModuleData R α) (x y : α) :
    letI : AddCommGroup α := D.1
    letI : Module R α := D.2
    let Dβ : AddModuleData R β := h.rec D
    letI : AddCommGroup β := Dβ.1
    letI : Module R β := Dβ.2
    cast h (x + y) = cast h x + cast h y := by
  cases h
  rfl

/-- Casting along `h.symm` is additive for the structure on `α` and its transport to `β`. -/
theorem cast_symm_add_rec {R : Type u} [CommRing R] {α β : Type v₁} (h : α = β)
    (D : AddModuleData R α) (x y : β) :
    letI : AddCommGroup α := D.1
    letI : Module R α := D.2
    let Dβ : AddModuleData R β := h.rec D
    letI : AddCommGroup β := Dβ.1
    letI : Module R β := Dβ.2
    cast h.symm (x + y) = cast h.symm x + cast h.symm y := by
  cases h
  rfl

/-- Casting along `h` commutes with scalar multiplication for the structure on `α` and its
transport to `β`. -/
theorem cast_smul_rec {R : Type u} [CommRing R] {α β : Type v₁} (h : α = β)
    (D : AddModuleData R α) (r : R) (x : α) :
    letI : AddCommGroup α := D.1
    letI : Module R α := D.2
    let Dβ : AddModuleData R β := h.rec D
    letI : AddCommGroup β := Dβ.1
    letI : Module R β := Dβ.2
    cast h (r • x) = r • cast h x := by
  cases h
  rfl

/-- Casting along `h.symm` commutes with scalar multiplication for the structure on `α` and its
transport to `β`. -/
theorem cast_symm_smul_rec {R : Type u} [CommRing R] {α β : Type v₁} (h : α = β)
    (D : AddModuleData R α) (r : R) (x : β) :
    letI : AddCommGroup α := D.1
    letI : Module R α := D.2
    let Dβ : AddModuleData R β := h.rec D
    letI : AddCommGroup β := Dβ.1
    letI : Module R β := Dβ.2
    cast h.symm (r • x) = r • cast h.symm x := by
  cases h
  rfl

/-- **Stacks Project, Tag 06IJ.** The differential of a morphism of predeformation categories
is `k`-linear for the natural tangent-space vector structures when both associated functors
satisfy (S2). -/
@[stacks 06IJ]
theorem differential_isLinearMap
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2𝓕 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (hS2𝓖 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (φ : BasedFunctor 𝓕 𝓖) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
    IsLinearMap k (differential h𝓕.cofibered h𝓖.cofibered φ) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
  let P := artinianLocalOver Λ k
  let hP := squareZeroExtension_mem_artinianLocalOver Λ k
  let q := squareZeroExtensionRestriction Λ k P hP
  let a := artinianLocalOverToArtinian Λ k
  let IF := a ⋙ isomorphismClasses 𝓕 h𝓕.cofibered
  let IG := a ⋙ isomorphismClasses 𝓖 h𝓖.cofibered
  let UF := tangentSpaceSetFunctor Λ k P hP IF
  let UG := tangentSpaceSetFunctor Λ k P hP IG
  let LF := associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2𝓕
  let LG := associatedTangentSpaceModuleStructureUnlifted 𝓖 h𝓖 hS2𝓖
  let eF (M : FGModuleCat.{w} k) : (LF.functor.obj M : Type u₁) = UF.obj M :=
    congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj M) LF.forget_comp
  let eG (M : FGModuleCat.{w} k) : (LG.functor.obj M : Type u₂) = UG.obj M :=
    congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₂ => H.obj M) LG.forget_comp
  let tset : ∀ M : FGModuleCat.{w} k, UF.obj M → UG.obj M := fun M z =>
    mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ (a.obj (q.obj M)) z
  have htset : ∀ {M N : FGModuleCat.{w} k} (f : M ⟶ N) (z : UF.obj M),
      tset N (UF.map f z) = UG.map f (tset M z) := by
    intro M N f z
    dsimp [tset, UF, UG, tangentSpaceSetFunctor, q, a, IF, IG]
    exact mapIsomorphismClasses_naturality h𝓕.cofibered h𝓖.cofibered φ
      ((artinianLocalOverToArtinian Λ k).map
        ((squareZeroExtensionRestriction Λ k P hP).map f)) z
  let tmod : ∀ M : FGModuleCat.{w} k, LF.functor.obj M → LG.functor.obj M := fun M x =>
    cast (eG M).symm (tset M (cast (eF M) x))
  have htmod : ∀ {M N : FGModuleCat.{w} k} (f : M ⟶ N) (x : LF.functor.obj M),
      tmod N ((LF.functor.map f) x) = (LG.functor.map f) (tmod M x) := by
    intro M N f x
    dsimp [tmod]
    rw [moduleFunctor_map_cast k LF.functor UF LF.forget_comp f x, htset f]
    have hh := moduleFunctor_map_cast k LG.functor UG LG.forget_comp f
      (cast (eG M).symm (tset M (cast (eF M) x)))
    simpa [eF, eG] using (congrArg (cast (eG N).symm) hh).symm
  have hlin := isLinearMap_of_natural_on_fgModules k LF.functor LG.functor tmod htmod
  let A : FGModuleCat.{w} k := FGModuleCat.of k k
  have hFcarrier := associatedTangentSpaceModuleStructure_carrierUnlifted 𝓕 h𝓕 hS2𝓕
  have hGcarrier := associatedTangentSpaceModuleStructure_carrierUnlifted 𝓖 h𝓖 hS2𝓖
  have heF : eF A = hFcarrier := Subsingleton.elim _ _
  have heG : eG A = hGcarrier := Subsingleton.elim _ _
  dsimp [tmod, eF, eG] at hlin
  rw [heF, heG] at hlin
  let dmod : LF.functor.obj A → LG.functor.obj A := fun z =>
    cast hGcarrier.symm (tset A (cast hFcarrier z))
  change IsLinearMap k dmod at hlin
  have hmap : mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ (a.obj (q.obj A)) =
      mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
        (augmentedDualNumbers (Λ := Λ) (k := k)) := rfl
  let DF : AddModuleData k (LF.functor.obj A) := ⟨inferInstance, inferInstance⟩
  let DG : AddModuleData k (LG.functor.obj A) := ⟨inferInstance, inferInstance⟩
  have hFcancel (x : artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      cast (eF A) (cast hFcarrier.symm x) = x := by
    rw [heF]
    exact cast_symm_cancel hFcarrier x
  have hdiff (x : artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      differential h𝓕.cofibered h𝓖.cofibered φ x =
        cast hGcarrier (dmod (cast hFcarrier.symm x)) := by
    change mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
        (augmentedDualNumbers (Λ := Λ) (k := k)) x =
      cast hGcarrier (cast (eG A).symm
        (mapIsomorphismClasses h𝓕.cofibered h𝓖.cofibered φ
          (a.obj (q.obj A)) (cast (eF A) (cast hFcarrier.symm x))))
    conv_lhs => rw [← hmap]
    rw [hFcancel, heG]
    exact (cast_symm_cancel hGcarrier _).symm
  have hFadd (x y : artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      cast hFcarrier.symm (x + y) =
        cast hFcarrier.symm x + cast hFcarrier.symm y := by
    exact cast_symm_add_rec hFcarrier DF x y
  have hFsmul (r : k) (x : artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) :
      cast hFcarrier.symm (r • x) = r • cast hFcarrier.symm x := by
    exact cast_symm_smul_rec hFcarrier DF r x
  have hGadd (x y : LG.functor.obj A) :
      cast hGcarrier (x + y) = cast hGcarrier x + cast hGcarrier y := by
    exact cast_add_rec hGcarrier DG x y
  have hGsmul (r : k) (x : LG.functor.obj A) :
      cast hGcarrier (r • x) = r • cast hGcarrier x := by
    exact cast_smul_rec hGcarrier DG r x
  constructor
  · intro x y
    rw [hdiff, hdiff, hdiff, hFadd, hlin.map_add, hGadd]
  · intro r x
    rw [hdiff, hdiff, hFsmul, hlin.map_smul, hGsmul]

end

end Deformation
