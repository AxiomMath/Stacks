module

public import StacksFrontier.Deformation.Artin.FormalObject

/-!
# Formal objects which are not effective, detected by classifying invariants

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and let `P` be a presheaf of sets on
the big fppf site of `S`. A *classifying invariant* of `𝒳` with values in `P` assigns to every
object `z` of `𝒳` lying over `U` an element `cl z ∈ P(U)` such that

* `cl` is natural: for `φ : z' ⟶ z` lying over `g : U' ⟶ U`, `cl z' = g^* (cl z)`;
* every element of `P(U)` is the invariant of some object over `U` (up to an isomorphism of
  `U`);
* two objects with the same invariant (up to an isomorphism `e` of their bases) are related by a
  morphism lying over `e`.

The motivating example is the stack `[S/A]` of torsors under an abelian group scheme `A` with
`P = H¹(-, A)`: Stacks 03AJ says that the isomorphism classes of `A`-torsors over `U` are
`H¹(U, A)`.

For a formal object `ξ` over a complete local base `R`, the invariants of its levels form a
compatible system in `lim P(Spec R / 𝔪ⁿ⁺¹)`. If `ξ` is effective, this system is the restriction
of a single element of `P(Spec R)`: an isomorphism of formal objects onto the approximation of an
object `x` over some complete local base `R'` gives, by Stacks 07X4, a map of bases
`Spec R ⟶ Spec R'`, along which the invariant of `x` pulls back. Conversely, every compatible
system of elements is the system of invariants of some formal object. Hence a compatible system
which is not the restriction of any element of `P(Spec R)` gives a formal object which is not
effective, in the sense of Stacks 07X7.

## Main definitions

* `Deformation.Artin.IsClassifyingInvariant`: the three conditions above.
* `Deformation.Artin.formalObjectOfCompatible`: the formal object built from a compatible system
  of elements.

## Main results

* `Deformation.Artin.not_isEffective_of_classes`: a formal object whose system of invariants is
  not the restriction of an element over the complete local base is not effective.
* `Deformation.Artin.exists_not_isEffective_of_compatible`: a compatible system which is not the
  restriction of any element over the base gives a formal object which is not effective.
* `Deformation.Artin.exists_not_restriction_of_compatible`: the same system gives a formal object
  over the base which is not the system of restrictions of an object over the base.
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory Opposite IsLocalRing Functor

universe u v w t

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- A *classifying invariant* of a category `p : F ⥤ (Sch/S)_fppf` with values in a presheaf
`P`: an element `cl z ∈ P(p z)` for every object `z`, natural in `z`, which is surjective onto
every `P(U)` and which detects morphisms over isomorphisms of the base. -/
structure IsClassifyingInvariant (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t)
    (cl : ∀ z : F, P.obj (op (p.obj z))) : Prop where
  /-- The invariant is natural along morphisms of `F`. -/
  naturality : ∀ {z' z : F} (φ : z' ⟶ z), cl z' = P.map (p.map φ).op (cl z)
  /-- Every element is the invariant of an object, up to an isomorphism of the base. -/
  surjective : ∀ (U : BigFppfOver B S hS) (c : P.obj (op U)),
    ∃ (z : F) (e : p.obj z ≅ U), cl z = P.map e.hom.op c
  /-- Two objects whose invariants agree along an isomorphism of their bases are related by a
  morphism lying over that isomorphism. -/
  injective : ∀ (z₁ z₂ : F) (e : p.obj z₁ ≅ p.obj z₂), cl z₁ = P.map e.hom.op (cl z₂) →
    ∃ φ : z₁ ⟶ z₂, p.map φ = e.hom

namespace IsClassifyingInvariant

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}

/-- For a category fibred in groupoids, every element of `P(U)` is the invariant of an object
lying over `U` on the nose. -/
theorem surjective_strict (hcl : IsClassifyingInvariant P cl) (hp : p.IsFiberedInGroupoids)
    (U : BigFppfOver B S hS) (c : P.obj (op U)) :
    ∃ (z : F) (hz : p.obj z = U), cl z = P.map (eqToHom hz).op c := by
  obtain ⟨z, e, hz⟩ := hcl.surjective U c
  obtain ⟨z', φ, hφ⟩ := hp.exists_lift e.inv z rfl
  have hz' : p.obj z' = U := IsHomLift.domain_eq p e.inv φ
  refine ⟨z', hz', ?_⟩
  rw [hcl.naturality φ, hz, ← Functor.map_comp_apply, ← op_comp,
    IsHomLift.fac' p e.inv φ]
  simp

end IsClassifyingInvariant

variable (B S hS)

/-- The **Stacks 07X4** base map of a morphism `ξ ⟶ ζ` of formal objects, as a morphism of the
big fppf site between the spectra of their complete local bases. -/
def FormalObject.Hom.baseMapOver {ξ ζ : FormalObject B S hS p} (f : ξ ⟶ ζ)
    (hξ : B.Contains (Spec (.of ξ.base.R))) (hζ : B.Contains (Spec (.of ζ.base.R))) :
    baseOver B S hS ξ.base hξ ⟶ baseOver B S hS ζ.base hζ :=
  Over.homMk (ObjectProperty.homMk (X := B.obj hξ) (Y := B.obj hζ)
    (FormalObject.Hom.baseMap (B := B) (S := S) (hS := hS) (p := p) f))
    (ObjectProperty.hom_ext _ (FormalObject.Hom.baseMap_spec f).1)

/-- The base map of a morphism of formal objects restricts, on the `n`-th thickenings, to the
image under `p` of the `n`-th component of the morphism. -/
theorem FormalObject.Hom.restrictionToBase_baseMapOver {ξ ζ : FormalObject B S hS p} (f : ξ ⟶ ζ)
    (hξ : B.Contains (Spec (.of ξ.base.R))) (hζ : B.Contains (Spec (.of ζ.base.R))) (n : ℕ) :
    restrictionToBase B S hS ξ.base hξ ξ.contains n ≫ f.baseMapOver B S hS hξ hζ =
      (eqToHom (ξ.level_eq n).symm ≫ p.map (f.app n) ≫ eqToHom (ζ.level_eq n)) ≫
        restrictionToBase B S hS ζ.base hζ ζ.contains n := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, restrictionToBase_toScheme,
    restrictionToBase_toScheme]
  exact ((FormalObject.Hom.baseMap_spec f).2 n).symm

/-- Formal bases which are equal have spectra which agree over `S`. -/
theorem FormalBase.eqToHom_toS {A₁ A₂ : FormalBase S} (h : A₁ = A₂) :
    eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) h) ≫ A₂.toS = A₁.toS := by
  subst h
  simp

/-- The object over a complete local base underlying an object of `CompleteLocalObjects`
lies over the base of its approximation. -/
theorem approximationFunctor_base_eq (hp : p.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) :
    ∃ (hx : B.Contains (Spec (.of ((approximationFunctor B S hS p hp).obj x).base.R)))
      (r : ∀ n, ((approximationFunctor B S hS p hp).obj x).level n ⟶ x.obj.1)
      (β : baseOver B S hS ((approximationFunctor B S hS p hp).obj x).base hx ⟶ p.obj x.obj.1),
      ∀ n, eqToHom (((approximationFunctor B S hS p hp).obj x).level_eq n).symm ≫ p.map (r n) =
        restrictionToBase B S hS _ hx (((approximationFunctor B S hS p hp).obj x).contains) n ≫
          β := by
  obtain ⟨r, hbase, -, -, -, hscheme⟩ := (approximationFunctorData B S hS p hp).2
  set G := approximationFunctor B S hS p hp
  have hx : B.Contains (Spec (.of (G.obj x).base.R)) := by
    rw [hbase x]; exact chosenContains B S hS p x.obj
  let e : Spec (.of (G.obj x).base.R) ⟶ Spec (.of (chosenBase B S hS p x.obj).R) :=
    eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R)) (hbase x))
  let β₀ : baseOver B S hS (G.obj x).base hx ⟶
      baseOver B S hS (chosenBase B S hS p x.obj) (chosenContains B S hS p x.obj) :=
    Over.homMk (ObjectProperty.homMk (X := B.obj hx) (Y := B.obj (chosenContains B S hS p x.obj))
      e) (ObjectProperty.hom_ext _ (FormalBase.eqToHom_toS S (hbase x)))
  refine ⟨hx, r x, β₀ ≫ eqToHom (chosenBase_eq B S hS p x.obj).symm, fun n ↦ ?_⟩
  apply (BigFppfOver.toScheme B S hS).map_injective
  have h' : (BigFppfOver.toScheme B S hS).map (eqToHom ((G.obj x).level_eq n).symm) ≫
      (BigFppfOver.toScheme B S hS).map (p.map (r x n)) =
      (adicThickeningι (G.obj x).base.R (maximalIdeal (G.obj x).base.R) n ≫ e) ≫
        (BigFppfOver.toScheme B S hS).map (eqToHom (chosenBase_eq B S hS p x.obj).symm) := by
    calc _ = ((BigFppfOver.toScheme B S hS).map (eqToHom ((G.obj x).level_eq n).symm) ≫
          (BigFppfOver.toScheme B S hS).map (p.map (r x n)) ≫
          (BigFppfOver.toScheme B S hS).map (eqToHom (chosenBase_eq B S hS p x.obj))) ≫
          (BigFppfOver.toScheme B S hS).map (eqToHom (chosenBase_eq B S hS p x.obj).symm) := by
          simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
            eqToHom_refl, Category.comp_id]
      _ = _ := by
          rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
          exact congrArg (· ≫ _) (hscheme x n)
  simp only [Functor.map_comp]
  rw [restrictionToBase_toScheme, h']
  exact Category.assoc _ _ _

variable {B S hS}

/-- **A formal object whose invariants do not come from the base is not effective.** Let `ξ` be a
formal object, over a complete local base `R` whose spectrum lies in the site, of a category
fibred in groupoids with a classifying invariant `cl`. If no element of `P(Spec R)` restricts to
the invariants of all levels of `ξ`, then `ξ` is not effective in the sense of Stacks 07X7. -/
theorem not_isEffective_of_classes (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (ξ : FormalObject B S hS p)
    (hξ : B.Contains (Spec (.of ξ.base.R)))
    (hnot : ∀ y : P.obj (op (baseOver B S hS ξ.base hξ)), ∃ n,
      P.map (eqToHom (ξ.level_eq n) ≫ (restrictionToBase B S hS ξ.base hξ ξ.contains n :
        truncationOver B S hS ξ.base ξ.contains n ⟶ _)).op y ≠ cl (ξ.level n)) :
    ¬ FormalObject.IsEffective B S hS p hp ξ := by
  rintro ⟨x, ⟨e⟩⟩
  obtain ⟨hx, r, β, hβ⟩ := approximationFunctor_base_eq B S hS hp x
  obtain ⟨n, hn⟩ := hnot (P.map (e.inv.baseMapOver B S hS hξ hx ≫ β).op (cl x.obj.1))
  apply hn
  have key : (eqToHom (ξ.level_eq n) ≫ restrictionToBase B S hS ξ.base hξ ξ.contains n) ≫
      (e.inv.baseMapOver B S hS hξ hx ≫ β) = p.map (e.inv.app n ≫ r n) := by
    rw [Category.assoc, ← Category.assoc (restrictionToBase B S hS ξ.base hξ ξ.contains n),
      FormalObject.Hom.restrictionToBase_baseMapOver, Category.assoc, Category.assoc,
      Category.assoc, ← hβ n]
    simp
  rw [← Functor.map_comp_apply, ← op_comp, key, ← hcl.naturality]

/-! ### Formal objects from compatible systems -/

/-- The level of the formal object attached to a compatible system: an object over the `n`-th
thickening with the prescribed invariant. -/
def levelOfCompatible (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n))) (n : ℕ) : F :=
  (hcl.surjective_strict hp _ (s n)).choose

theorem levelOfCompatible_eq (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n))) (n : ℕ) :
    p.obj (levelOfCompatible hp hcl A contains s n) = truncationOver B S hS A contains n :=
  (hcl.surjective_strict hp _ (s n)).choose_spec.choose

theorem cl_levelOfCompatible (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n))) (n : ℕ) :
    cl (levelOfCompatible hp hcl A contains s n) =
      P.map (eqToHom (levelOfCompatible_eq hp hcl A contains s n)).op (s n) :=
  (hcl.surjective_strict hp _ (s n)).choose_spec.choose_spec

/-- For a compatible system, the next level restricted to the `n`-th thickening receives a
morphism from the `n`-th level lying over the transition of the thickenings. -/
theorem exists_transitionOfCompatible (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n)))
    (hs : ∀ n, P.map (truncationOverSucc B S hS A contains n).op (s (n + 1)) = s n) (n : ℕ) :
    ∃ φ : levelOfCompatible hp hcl A contains s n ⟶ levelOfCompatible hp hcl A contains s (n + 1),
      p.IsHomLift (truncationOverSucc B S hS A contains n) φ := by
  set z := levelOfCompatible hp hcl A contains s
  have hz := levelOfCompatible_eq hp hcl A contains s
  obtain ⟨w, ψ, hψ⟩ := hp.exists_lift (truncationOverSucc B S hS A contains n) (z (n + 1))
    (hz (n + 1))
  have hw : p.obj w = truncationOver B S hS A contains n :=
    IsHomLift.domain_eq p (truncationOverSucc B S hS A contains n) ψ
  have hcl' : cl (z n) = P.map (eqToHom ((hz n).trans hw.symm)).op (cl w) := by
    rw [hcl.naturality ψ, cl_levelOfCompatible hp hcl A contains s n,
      cl_levelOfCompatible hp hcl A contains s (n + 1),
      IsHomLift.fac' p (truncationOverSucc B S hS A contains n) ψ, ← hs n]
    simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc, eqToHom_refl, Category.comp_id]
  obtain ⟨χ, hχ⟩ := hcl.injective (z n) w (eqToIso ((hz n).trans hw.symm)) hcl'
  refine ⟨χ ≫ ψ, ?_⟩
  have : p.IsHomLift (𝟙 (truncationOver B S hS A contains n)) χ :=
    IsHomLift.of_fac' p _ _ (hz n) hw (by simp [hχ])
  simpa using (inferInstance :
    p.IsHomLift (𝟙 (truncationOver B S hS A contains n) ≫
      truncationOverSucc B S hS A contains n) (χ ≫ ψ))

/-- The formal object attached to a compatible system of elements of `P` on the thickenings of
a complete local base: its levels have the prescribed invariants. -/
def formalObjectOfCompatible (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n)))
    (hs : ∀ n, P.map (truncationOverSucc B S hS A contains n).op (s (n + 1)) = s n) :
    FormalObject B S hS p where
  base := A
  contains := contains
  level := levelOfCompatible hp hcl A contains s
  level_eq := levelOfCompatible_eq hp hcl A contains s
  transition n := (exists_transitionOfCompatible hp hcl A contains s hs n).choose
  transition_lift n := (exists_transitionOfCompatible hp hcl A contains s hs n).choose_spec

/-- **A compatible system which does not come from the base gives a formal object which is not
effective.** For a category fibred in groupoids with a classifying invariant with values in `P`,
and a compatible system `s` of elements of `P` on the thickenings of a complete local base `R`
whose spectrum lies in the site, if no element of `P(Spec R)` restricts to `s`, then there is a
formal object over `R` which is not effective in the sense of Stacks 07X7. -/
theorem exists_not_isEffective_of_compatible (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n)))
    (hs : ∀ n, P.map (truncationOverSucc B S hS A contains n).op (s (n + 1)) = s n)
    (hnot : ∀ y : P.obj (op (baseOver B S hS A hA)), ∃ n,
      P.map (restrictionToBase B S hS A hA contains n).op y ≠ s n) :
    ∃ ξ : FormalObject B S hS p, ¬ FormalObject.IsEffective B S hS p hp ξ := by
  refine ⟨formalObjectOfCompatible hp hcl A contains s hs,
    not_isEffective_of_classes hp hcl _ hA fun y ↦ ?_⟩
  obtain ⟨n, hn⟩ := hnot y
  refine ⟨n, fun h ↦ hn ?_⟩
  change P.map (eqToHom (levelOfCompatible_eq hp hcl A contains s n) ≫
    restrictionToBase B S hS A hA contains n).op y = cl (levelOfCompatible hp hcl A contains s n)
    at h
  rw [cl_levelOfCompatible hp hcl A contains s n] at h
  simp only [op_comp, Functor.map_comp] at h
  exact ((CategoryTheory.isIso_iff_bijective
    (P.map (eqToHom (levelOfCompatible_eq hp hcl A contains s n)).op)).mp inferInstance).1 h

/-- **A compatible system which does not come from the base gives a formal object which is not
a restriction.** For a category fibred in groupoids with a classifying invariant with values in
`P`, and a compatible system `s` of elements of `P` on the thickenings `Spec R/𝔪ⁿ⁺¹` of a
complete local base `R` whose spectrum lies in the site, if no element of `P(Spec R)` restricts
to `s`, then there is a formal object `ξ` over `R`, i.e. an object of `lim 𝒳(Spec R/𝔪ⁿ⁺¹)`, which
is not isomorphic to the system of restrictions of an object `x` over `Spec R`: there is no
object `x` with morphisms `ξₙ ⟶ x` lying over the closed immersions `Spec R/𝔪ⁿ⁺¹ ⟶ Spec R`. In a
category fibred in groupoids such morphisms are exactly the identifications of `ξₙ` with the
restrictions of `x`. -/
theorem exists_not_restriction_of_compatible (hp : p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl : ∀ z : F, P.obj (op (p.obj z))}
    (hcl : IsClassifyingInvariant P cl) (A : FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (contains : ∀ n, B.Contains (A.truncation n))
    (s : ∀ n, P.obj (op (truncationOver B S hS A contains n)))
    (hs : ∀ n, P.map (truncationOverSucc B S hS A contains n).op (s (n + 1)) = s n)
    (hnot : ∀ y : P.obj (op (baseOver B S hS A hA)), ∃ n,
      P.map (restrictionToBase B S hS A hA contains n).op y ≠ s n) :
    ∃ ξ : FormalObject B S hS p, ξ.base = A ∧
      (∀ n, p.obj (ξ.level n) = truncationOver B S hS A contains n) ∧
      ∀ (x : F) (r : ∀ n, ξ.level n ⟶ x),
        ¬ ∀ n, p.IsHomLift (restrictionToBase B S hS A hA contains n) (r n) := by
  refine ⟨formalObjectOfCompatible hp hcl A contains s hs, rfl,
    levelOfCompatible_eq hp hcl A contains s, fun x r hr ↦ ?_⟩
  have hx : p.obj x = baseOver B S hS A hA := by
    have := hr 0
    exact IsHomLift.codomain_eq p (restrictionToBase B S hS A hA contains 0) (r 0)
  obtain ⟨n, hn⟩ := hnot (P.map (eqToHom hx.symm).op (cl x))
  apply hn
  have h : P.map (eqToHom (levelOfCompatible_eq hp hcl A contains s n) ≫
      restrictionToBase B S hS A hA contains n).op (P.map (eqToHom hx.symm).op (cl x)) =
      P.map (eqToHom (levelOfCompatible_eq hp hcl A contains s n)).op (s n) := by
    have := hr n
    refine Eq.trans ?_ ((hcl.naturality (r n)).symm.trans
      (cl_levelOfCompatible hp hcl A contains s n))
    rw [IsHomLift.fac' p (restrictionToBase B S hS A hA contains n) (r n),
      ← Functor.map_comp_apply, ← op_comp, Category.assoc]
    rfl
  simp only [op_comp, Functor.map_comp] at h
  exact ((CategoryTheory.isIso_iff_bijective
    (P.map (eqToHom (levelOfCompatible_eq hp hcl A contains s n)).op)).mp inferInstance).1 h

/-! ### Transport along functors over the site -/

/-- **Classifying invariants transport along equivalences over the site.** Let `G : F ⥤ F'` be
a functor over the big fppf site (`G ⋙ q = p`) which is full and essentially surjective, for
instance the forward functor of an equivalence over the site. A classifying invariant `cl'` of
`q` induces a classifying invariant of `p`, the invariant of `z` being that of `G z`. -/
theorem IsClassifyingInvariant.comp {F' : Type*} [Category F'] {q : F' ⥤ BigFppfOver B S hS}
    (G : F ⥤ F') (hG : G ⋙ q = p) [G.Full] [G.EssSurj]
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type t} {cl' : ∀ z : F', P.obj (op (q.obj z))}
    (hcl' : IsClassifyingInvariant P cl') :
    IsClassifyingInvariant (p := p) P
      (fun z ↦ P.map (eqToHom (Functor.congr_obj hG z).symm).op (cl' (G.obj z))) where
  naturality := by
    intro z' z φ
    simp only
    rw [hcl'.naturality (G.map φ), Functor.congr_hom hG.symm φ]
    simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc, eqToHom_trans]
    congr 2
  surjective := by
    intro U c
    obtain ⟨z', e, hz'⟩ := hcl'.surjective U c
    let ε := G.objObjPreimageIso z'
    refine ⟨G.objPreimage z', eqToIso (Functor.congr_obj hG _).symm ≪≫ q.mapIso ε ≪≫ e, ?_⟩
    simp only
    rw [hcl'.naturality ε.hom, hz']
    simp only [← Functor.map_comp_apply, ← op_comp, Iso.trans_hom, eqToIso.hom,
      Functor.mapIso_hom]
  injective := by
    intro z₁ z₂ e he
    let e' : q.obj (G.obj z₁) ≅ q.obj (G.obj z₂) :=
      eqToIso (Functor.congr_obj hG z₁) ≪≫ e ≪≫ eqToIso (Functor.congr_obj hG z₂).symm
    obtain ⟨ψ, hψ⟩ := hcl'.injective (G.obj z₁) (G.obj z₂) e' (by
      have := congrArg (P.map (eqToHom (Functor.congr_obj hG z₁)).op) he
      simp only [← Functor.map_comp_apply, ← op_comp, eqToHom_trans, eqToHom_refl,
        op_id, Functor.map_id_apply] at this
      rw [this]
      simp only [e', Iso.trans_hom, eqToIso.hom])
    refine ⟨G.preimage ψ, ?_⟩
    rw [Functor.congr_hom hG.symm (G.preimage ψ), Functor.comp_map, Functor.map_preimage, hψ]
    simp [e']

end Deformation.Artin
