module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Quotient presentations of an inverse system in an abelian category

An inverse system `S : ℕᵒᵖ ⥤ C` in an abelian category is *presented* by a second system when
each `S_{index n}` surjects onto an object `P n` with kernel `ℓⁿ⁺¹ S_{index n}`, compatibly with
the transition maps. The objects `P n` then assemble into an inverse system `presentationTower P`
receiving a map from `S` in the pro-category sense, and that tower is the normalised replacement
of `S`: its level `n` is killed by `ℓⁿ⁺¹`.

## Main definitions

* `CategoryTheory.scalarCokernelMap` is the map `X/rX ⟶ Y/rY` induced by `f : X ⟶ Y`.
* `CategoryTheory.QuotientPresentation` is the data presenting an inverse system as above.
* `CategoryTheory.presentationTower` is the inverse system of the presented objects.
* `CategoryTheory.presentationMap` and `CategoryTheory.presentationLift` are the universal maps
  out of and into that tower.

## Main results

* `CategoryTheory.scalarQuotient_comp_isCokernel` and
  `CategoryTheory.scalarQuotient_desc_isCokernel` transport the property of being a quotient by
  `r` along a composition, respectively a descent.
* `CategoryTheory.presentationMap_pro_mono`: the kernel of `presentationMap` at a high enough
  level dies under a transition map.
* `CategoryTheory.towerHom_eq_zero_of_pro_mono`: a map of towers `a : A ⟶ K` with `a ≫ j = 0` is
  zero, when the transition maps of `A` are epimorphisms and the kernels of `j` die under the
  transition maps of `K`.
* `CategoryTheory.presentationLift_map`: the lift into the tower is compatible with the map out
  of it.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

section ScalarQuotient

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The map `X/rX ⟶ Y/rY` induced by a morphism `f : X ⟶ Y`, multiplication by `r` being
natural. -/
public def scalarCokernelMap (r : ℕ) {X Y : C} (f : X ⟶ Y) :
    cokernel (r • (𝟙 X)) ⟶ cokernel (r • (𝟙 Y)) :=
  cokernel.map _ _ f f (by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])

/-- The defining square of `CategoryTheory.scalarCokernelMap`. -/
public theorem scalarCokernelMap_fac (r : ℕ) {X Y : C} (f : X ⟶ Y) :
    cokernel.π (r • (𝟙 X)) ≫ scalarCokernelMap r f = f ≫ cokernel.π (r • (𝟙 Y)) := by
  simp [scalarCokernelMap, cokernel.map]

/-- For an epimorphism whose kernel is already contained in `rX`, the induced map on the
quotients by `r` is an isomorphism. -/
public theorem scalarCokernelMap_isIso (r : ℕ) {X Y : C} (f : X ⟶ Y) [Epi f]
    (h : kernel.ι f ≫ cokernel.π (r • (𝟙 X)) = 0) :
    IsIso (scalarCokernelMap r f) := by
  let d := Abelian.epiDesc f (cokernel.π (r • (𝟙 X))) h
  have hd : f ≫ d = cokernel.π (r • (𝟙 X)) := Abelian.comp_epiDesc _ _ _
  have hd0 : (r • (𝟙 Y)) ≫ d = 0 := by
    apply (cancel_epi f).1
    rw [comp_zero, ← Category.assoc, Preadditive.comp_nsmul, Category.comp_id,
      Preadditive.nsmul_comp, hd]
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using cokernel.condition (r • (𝟙 X))
  let g := cokernel.desc (r • (𝟙 Y)) d hd0
  have hg : scalarCokernelMap r f ≫ g = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (r • (𝟙 X)))).1
    rw [← Category.assoc, scalarCokernelMap_fac, Category.assoc, cokernel.π_desc, hd,
      Category.comp_id]
  have : Epi (scalarCokernelMap r f) := epi_of_epi_fac (scalarCokernelMap_fac r f)
  refine ⟨⟨g, hg, ?_⟩⟩
  apply (cancel_epi (scalarCokernelMap r f)).1
  rw [← Category.assoc, hg, Category.id_comp, Category.comp_id]

/-- The comparison of kernels along a quotient map dies in the quotient by `r`.

Here `t` exhibits `F'` as `F/aF` with `a = r * b`, `i` is the kernel of an epimorphism `f`, and
`tK` is the induced map on kernels. The hypothesis `hdiv` is a divisibility statement about maps
into `G` killed by `a`: multiplying such a map by `b` lands it in `sG`. Under it the kernel of
`tK` is carried into `rK`. -/
public theorem kernelTransition_scalar_quotient_zero
    {F G F' K K' : C} (f : F ⟶ G) [Epi f]
    (t : F ⟶ F') (a r b s : ℕ) (ha : a = r * b)
    (ht0 : (a • (𝟙 F)) ≫ t = 0)
    (ht : IsColimit (CokernelCofork.ofπ t ht0))
    (i : K ⟶ F) [Mono i] (hi0 : i ≫ f = 0)
    (hi : IsLimit (KernelFork.ofι i hi0))
    (tK : K ⟶ K') (j : K' ⟶ F')
    (fac : tK ≫ j = i ≫ t)
    (hchar : (r * s) • (𝟙 F) = 0)
    (hdiv : ∀ (A : C) (g : A ⟶ G), a • g = 0 →
      (b • g) ≫ cokernel.π (s • (𝟙 G)) = 0) :
    kernel.ι tK ≫ cokernel.π (r • (𝟙 K)) = 0 := by
  let x := kernel.ι tK
  have hx : (x ≫ i) ≫ t = 0 := by
    rw [Category.assoc, ← fac, ← Category.assoc, kernel.condition, zero_comp]
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements ht (x ≫ i)).1 hx
  have hy' : π₁ ≫ x ≫ i = a • y := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id] using hy
  have hyg : a • (y ≫ f) = 0 := by
    rw [← Preadditive.nsmul_comp, ← hy', Category.assoc, Category.assoc,
      hi0, comp_zero, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, z, hz⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
      (cokernelIsCokernel (s • (𝟙 G))) (b • (y ≫ f))).1 (hdiv _ _ hyg)
  have hz' : b • ((π₂ ≫ y) ≫ f) = s • z := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id, Category.assoc] using hz
  obtain ⟨A₃, π₃, hπ₃, w, hw⟩ := surjective_up_to_refinements_of_epi f z
  let v : A₃ ⟶ F := b • (π₃ ≫ π₂ ≫ y) - s • w
  have hv : v ≫ f = 0 := by
    dsimp only [v]
    rw [Preadditive.sub_comp, Preadditive.nsmul_comp, Preadditive.nsmul_comp,
      Category.assoc, ← Preadditive.comp_nsmul, hz', Preadditive.comp_nsmul, hw, sub_self]
  let vK := (KernelFork.IsLimit.lift' hi v hv).1
  have hvK : vK ≫ i = v := (KernelFork.IsLimit.lift' hi v hv).2
  have hw0 : (r * s) • w = 0 := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero] using
      congrArg (fun q => w ≫ q) hchar
  have he : (π₃ ≫ π₂ ≫ π₁) ≫ x = r • vK := by
    apply (cancel_mono i).1
    rw [Preadditive.nsmul_comp, hvK]
    dsimp only [v]
    rw [smul_sub, smul_smul, smul_smul, hw0, sub_zero, ← ha,
      Category.assoc, Category.assoc, Category.assoc, hy',
      Preadditive.comp_nsmul, Preadditive.comp_nsmul]
  apply (cancel_epi (π₃ ≫ π₂ ≫ π₁)).1
  rw [comp_zero, ← Category.assoc, he, Preadditive.nsmul_comp]
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
    comp_zero] using congrArg (fun q => vK ≫ q) (cokernel.condition (r • (𝟙 K)))

/-- A composite of two quotient maps, by `a` and then by `b` with `b ∣ a`, is the quotient by
`b`. -/
public def nsmulCokernel_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (a b : ℕ) (hba : b ∣ a)
    (hf0 : (a • (𝟙 X)) ≫ f = 0) (hg0 : (b • (𝟙 Y)) ≫ g = 0)
    (hf : IsColimit (CokernelCofork.ofπ f hf0))
    (hg : IsColimit (CokernelCofork.ofπ g hg0)) :
    IsColimit (CokernelCofork.ofπ (f ≫ g) (show (b • (𝟙 X)) ≫ (f ≫ g) = 0 from by
      simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
        Category.assoc, comp_zero] using congrArg (fun q => f ≫ q) hg0)) := by
  haveI : Epi f := Cofork.IsColimit.epi hf
  haveI : Epi g := Cofork.IsColimit.epi hg
  apply CokernelCofork.IsColimit.ofπ' (f ≫ g)
  intro W q hq
  have hbq : b • q = 0 := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using hq
  have haq : (a • (𝟙 X)) ≫ q = 0 := by
    obtain ⟨c, rfl⟩ := hba
    rw [Preadditive.nsmul_comp, Category.id_comp, Nat.mul_comm, ← smul_smul, hbq, smul_zero]
  let d := (CokernelCofork.IsColimit.desc' hf q haq).1
  have hd : f ≫ d = q := (CokernelCofork.IsColimit.desc' hf q haq).2
  have hd0 : (b • (𝟙 Y)) ≫ d = 0 := by
    apply (cancel_epi f).1
    rw [comp_zero, ← Category.assoc, Preadditive.comp_nsmul, Category.comp_id,
      Preadditive.nsmul_comp, hd, hbq]
  refine ⟨(CokernelCofork.IsColimit.desc' hg d hd0).1, ?_⟩
  have he : g ≫ (CokernelCofork.IsColimit.desc' hg d hd0).1 = d :=
    (CokernelCofork.IsColimit.desc' hg d hd0).2
  rw [Category.assoc, he, hd]

/-- An additive right exact functor carries a quotient by `r` to a quotient by `r`. -/
public def mapNsmulCokernel {D : Type u} [Category.{v} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {X Y : C} (r : ℕ) (q : X ⟶ Y) (hq : (r • (𝟙 X)) ≫ q = 0)
    (h : IsColimit (CokernelCofork.ofπ q hq)) :
    IsColimit (CokernelCofork.ofπ (F.map q)
      (show (r • (𝟙 (F.obj X))) ≫ F.map q = 0 from by
        rw [← F.map_id, ← F.map_nsmul, ← F.map_comp, hq, F.map_zero])) := by
  have hm := CokernelCofork.mapIsColimit _ h F
  haveI : Epi q := Cofork.IsColimit.epi h
  apply CokernelCofork.IsColimit.ofπ'
  intro W k hk
  have hk' : F.map (r • (𝟙 X)) ≫ k = 0 := by
    rwa [F.map_nsmul, F.map_id]
  exact CokernelCofork.IsColimit.desc' hm k hk'

/-- If `a ≫ b` is an epimorphism and `t` kills the kernel of the epimorphism `b`, then `a ≫ t`
is an epimorphism: `t` factors through `b`. -/
public theorem epi_comp_of_kernel_annihilated {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (t : B ⟶ E)
    [Epi b] [Epi t] [Epi (a ≫ b)] (h : kernel.ι b ≫ t = 0) : Epi (a ≫ t) := by
  let d := Abelian.epiDesc b t h
  have hd : b ≫ d = t := Abelian.comp_epiDesc _ _ _
  have : Epi d := epi_of_epi_fac hd
  rw [← hd, ← Category.assoc]
  infer_instance

/-- Any object exhibited as a quotient of `X` by `r` is canonically `X/rX`. -/
public def scalarCokernelIso {X P : C} (r : ℕ) (q : X ⟶ P) (hq : (r • (𝟙 X)) ≫ q = 0)
    (h : IsColimit (CokernelCofork.ofπ q hq)) : cokernel (r • (𝟙 X)) ≅ P :=
  (cokernelIsCokernel (r • (𝟙 X))).coconePointUniqueUpToIso h

/-- The isomorphism of `CategoryTheory.scalarCokernelIso` identifies the two projections. -/
public theorem scalarCokernelIso_fac {X P : C} (r : ℕ) (q : X ⟶ P) (hq : (r • (𝟙 X)) ≫ q = 0)
    (h : IsColimit (CokernelCofork.ofπ q hq)) :
    cokernel.π (r • (𝟙 X)) ≫ (scalarCokernelIso r q hq h).hom = q :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (r • (𝟙 X))) h
    WalkingParallelPair.one

/-- A map of quotients by `r` induced by `t` is an isomorphism as soon as the canonical one
is. -/
public theorem scalarQuotientMap_isIso {X Y P Q : C} (r : ℕ) (t : X ⟶ Y)
    (p : X ⟶ P) (q : Y ⟶ Q)
    (hp : (r • (𝟙 X)) ≫ p = 0) (hq : (r • (𝟙 Y)) ≫ q = 0)
    (hp' : IsColimit (CokernelCofork.ofπ p hp))
    (hq' : IsColimit (CokernelCofork.ofπ q hq))
    (a : P ⟶ Q) (ha : p ≫ a = t ≫ q)
    [IsIso (scalarCokernelMap r t)] : IsIso a := by
  let ep := scalarCokernelIso r p hp hp'
  let eq := scalarCokernelIso r q hq hq'
  have hep : p ≫ ep.inv = cokernel.π (r • (𝟙 X)) := by
    rw [← scalarCokernelIso_fac r p hp hp', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : Epi p := Cofork.IsColimit.epi hp'
  have he : a = ep.inv ≫ scalarCokernelMap r t ≫ eq.hom := by
    apply (cancel_epi p).1
    rw [ha, ← Category.assoc, ← Category.assoc, hep,
      scalarCokernelMap_fac, Category.assoc, scalarCokernelIso_fac]
  rw [he]
  infer_instance

/-- Taking the quotient by `r` is functorial. -/
public theorem scalarCokernelMap_comp (r : ℕ) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    scalarCokernelMap r (f ≫ g) = scalarCokernelMap r f ≫ scalarCokernelMap r g := by
  apply (cancel_epi (cokernel.π (r • (𝟙 X)))).1
  rw [scalarCokernelMap_fac, ← Category.assoc, scalarCokernelMap_fac,
    Category.assoc f (cokernel.π (r • (𝟙 Y))), scalarCokernelMap_fac, Category.assoc]

/-- Reduction modulo `r`, as an endofunctor of an abelian category. -/
public def scalarCokernelFunctor (C : Type u) [Category.{v} C] [Abelian C] (r : ℕ) : C ⥤ C where
  obj X := cokernel (r • (𝟙 X))
  map := scalarCokernelMap r
  map_id X := by
    apply (cancel_epi (cokernel.π (r • (𝟙 X)))).1
    rw [scalarCokernelMap_fac, Category.id_comp, Category.comp_id]
  map_comp := scalarCokernelMap_comp r

/-- Precomposing a quotient by `r` with a map which is an isomorphism on the quotients by `r`
again gives a quotient by `r`. -/
public def scalarQuotient_comp_isCokernel {X Y P : C} (r : ℕ) (t : X ⟶ Y) (q : Y ⟶ P)
    (hq : (r • (𝟙 Y)) ≫ q = 0) (h : IsColimit (CokernelCofork.ofπ q hq))
    [IsIso (scalarCokernelMap r t)] :
    IsColimit (CokernelCofork.ofπ (t ≫ q) (show (r • (𝟙 X)) ≫ (t ≫ q) = 0 from by
      simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
        Category.assoc, comp_zero] using congrArg (fun z => t ≫ z) hq)) := by
  let e := asIso (scalarCokernelMap r t) ≪≫ scalarCokernelIso r q hq h
  apply cokernel.cokernelIso (r • (𝟙 X)) (t ≫ q) e
  change cokernel.π (r • (𝟙 X)) ≫ (scalarCokernelMap r t ≫ _) = _
  rw [← Category.assoc, scalarCokernelMap_fac, Category.assoc, scalarCokernelIso_fac]

/-- A map descended from a quotient by `r` along an epimorphism is itself a quotient by `r`. -/
public def scalarQuotient_desc_isCokernel {X P Q : C} (r : ℕ) (p : X ⟶ P) [Epi p] (q : X ⟶ Q)
    (hq : (r • (𝟙 X)) ≫ q = 0) (h : IsColimit (CokernelCofork.ofπ q hq))
    (t : P ⟶ Q) (ht : p ≫ t = q) :
    IsColimit (CokernelCofork.ofπ t (show (r • (𝟙 P)) ≫ t = 0 from by
      apply (cancel_epi p).1
      rw [comp_zero, ← Category.assoc, Preadditive.comp_nsmul, Category.comp_id,
        Preadditive.nsmul_comp, ht]
      simpa only [Preadditive.nsmul_comp, Category.id_comp] using hq)) := by
  haveI : Epi q := Cofork.IsColimit.epi h
  haveI : Epi t := epi_of_epi_fac ht
  apply CokernelCofork.IsColimit.ofπ'
  intro Z a ha
  have hpa : (r • (𝟙 X)) ≫ (p ≫ a) = 0 := by
    simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
      Category.assoc, comp_zero] using congrArg (fun z => p ≫ z) ha
  let d := CokernelCofork.IsColimit.desc' h (p ≫ a) hpa
  refine ⟨d.1, (cancel_epi p).1 ?_⟩
  rw [← Category.assoc, ht]
  exact d.2

end ScalarQuotient

section InverseSystemSucc

variable {C : Type u} [Category.{v} C]

/-- A morphism property stable under composition and containing identities holds for every
transition map of an inverse system as soon as it holds for the one-step ones above the lower
index. -/
private theorem inverseSystem_map_mem_of_succ (S : ℕᵒᵖ ⥤ C) (W : MorphismProperty C)
    [W.IsMultiplicative] {n m : ℕ} (h : n ≤ m)
    (hs : ∀ k : ℕ, n ≤ k → W (S.map (homOfLE (Nat.le_succ k)).op)) :
    W (S.map (homOfLE h).op) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl n)).op = 𝟙 _ from rfl, S.map_id]
    exact W.id_mem _
  | succ k h ih =>
    have he : (homOfLE (h.trans (Nat.le_succ k))).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := rfl
    rw [he, S.map_comp]
    exact W.comp_mem _ _ (hs k h) ih

/-- A transition map of an inverse system is an isomorphism as soon as every one-step transition
above the lower index is. -/
public theorem inverseSystem_map_isIso_of_succ (S : ℕᵒᵖ ⥤ C) {n m : ℕ} (h : n ≤ m)
    (hs : ∀ k : ℕ, n ≤ k → IsIso (S.map (homOfLE (Nat.le_succ k)).op)) :
    IsIso (S.map (homOfLE h).op) :=
  inverseSystem_map_mem_of_succ S (MorphismProperty.isomorphisms C) h hs

/-- A transition map of an inverse system is an epimorphism as soon as every one-step transition
is. -/
public theorem inverseSystem_map_epi_of_succ (S : ℕᵒᵖ ⥤ C)
    (hs : ∀ k : ℕ, Epi (S.map (homOfLE (Nat.le_succ k)).op)) {n m : ℕ} (h : n ≤ m) :
    Epi (S.map (homOfLE h).op) :=
  inverseSystem_map_mem_of_succ S (MorphismProperty.epimorphisms C) h fun k _ => hs k

end InverseSystemSucc

section TowerNormalization

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The object of an inverse system at a level. -/
public abbrev towerObj (S : ℕᵒᵖ ⥤ C) (n : ℕ) := S.obj (Opposite.op n)

/-- The transition map of an inverse system between two levels. -/
public abbrev towerMap (S : ℕᵒᵖ ⥤ C) {n m : ℕ} (h : n ≤ m) := S.map (homOfLE h).op

omit [Abelian C] in
/-- Transition maps of an inverse system compose. -/
public theorem towerMap_comp (S : ℕᵒᵖ ⥤ C) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    towerMap S hjk ≫ towerMap S hij = towerMap S (hij.trans hjk) := by
  rw [← S.map_comp]
  rfl

omit [Abelian C] in
/-- The transition map of an inverse system from a level to itself is the identity. -/
public theorem towerMap_self (S : ℕᵒᵖ ⥤ C) (n : ℕ) : towerMap S (le_refl n) = 𝟙 _ :=
  S.map_id _

/-- Multiplication by `r` on the source is killed by a map whose target is killed by `r`. -/
public theorem nsmul_hom_eq_zero {P Q : C} (r : ℕ) (f : P ⟶ Q) (h : r • (𝟙 Q) = 0) :
    (r • (𝟙 P)) ≫ f = 0 := by
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
    Category.comp_id, comp_zero] using congrArg (fun g => f ≫ g) h

/-- A quotient of an object by `r` is killed by `r`. -/
public theorem cokernel_annihilated {P Q : C} (r : ℕ) (q : P ⟶ Q) [Epi q]
    (h : (r • (𝟙 P)) ≫ q = 0) : r • (𝟙 Q) = 0 := by
  apply (cancel_epi q).1
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
    Category.comp_id, comp_zero] using h

/-- A presentation of an inverse system `S` as a tower of quotients killed by the successive
powers of `ℓ`: at each `n` a cofinal level `index n` of `S` is exhibited as an extension of
`obj n` by `ℓⁿ⁺¹`, stably in the level. -/
public structure QuotientPresentation (S : ℕᵒᵖ ⥤ C) (ℓ : ℕ) where
  /-- The presented object at each level. -/
  obj : ℕ → C
  /-- The level of `S` presenting `obj n`. -/
  index : ℕ → ℕ
  /-- The presenting level is at least the level presented. -/
  le_index : ∀ n, n ≤ index n
  /-- The presenting levels increase with the level presented. -/
  monotone_index : Monotone index
  /-- The presenting surjection. -/
  π : ∀ n, towerObj S (index n) ⟶ obj n
  /-- The presenting surjection kills `ℓⁿ⁺¹`. -/
  condition : ∀ n, ((ℓ ^ (n + 1)) • (𝟙 (towerObj S (index n)))) ≫ π n = 0
  /-- The presenting surjection exhibits `obj n` as the quotient by `ℓⁿ⁺¹`. -/
  isColimit : ∀ n, IsColimit (CokernelCofork.ofπ (π n) (condition n))
  /-- Above the presenting level, the quotients by `ℓⁿ⁺¹` no longer change. -/
  stable : ∀ n m (h : index n ≤ m), IsIso (scalarCokernelMap (ℓ ^ (n + 1)) (towerMap S h))

variable {S : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

/-- The presenting surjection of a quotient presentation is an epimorphism. -/
public theorem presentation_epi (P : QuotientPresentation (C := C) S ℓ) (n : ℕ) : Epi (P.π n) :=
  Cofork.IsColimit.epi (P.isColimit n)

attribute [local instance] presentation_epi

/-- The level `n` of a quotient presentation is killed by `ℓⁿ⁺¹`. -/
public theorem presentation_annihilated (P : QuotientPresentation (C := C) S ℓ) (n : ℕ) :
    ℓ ^ (n + 1) • (𝟙 (P.obj n)) = 0 :=
  cokernel_annihilated _ _ (P.condition n)

/-- The presenting surjection read from any level above the presenting one. -/
public def presentationAbove (P : QuotientPresentation (C := C) S ℓ) (n m : ℕ)
    (h : P.index n ≤ m) : towerObj S m ⟶ P.obj n := towerMap S h ≫ P.π n

/-- The surjection of `CategoryTheory.presentationAbove` kills `ℓⁿ⁺¹`. -/
public theorem presentationAbove_condition (P : QuotientPresentation (C := C) S ℓ) (n m : ℕ)
    (h : P.index n ≤ m) :
    ((ℓ ^ (n + 1)) • (𝟙 (towerObj S m))) ≫ presentationAbove P n m h = 0 :=
  nsmul_hom_eq_zero _ _ (presentation_annihilated P n)

/-- Above the presenting level, the presenting surjection still exhibits a quotient by
`ℓⁿ⁺¹`. -/
public def presentationAbove_isCokernel (P : QuotientPresentation (C := C) S ℓ) (n m : ℕ)
    (h : P.index n ≤ m) :
    IsColimit (CokernelCofork.ofπ (presentationAbove P n m h)
      (presentationAbove_condition P n m h)) := by
  haveI := P.stable n m h
  exact scalarQuotient_comp_isCokernel _ _ _ (P.condition n) (P.isColimit n)

/-- The transition map of the presented tower, descended from the transition maps of `S`. -/
public def presentationTransition (P : QuotientPresentation (C := C) S ℓ) (n : ℕ) :
    P.obj (n + 1) ⟶ P.obj n :=
  (CokernelCofork.IsColimit.desc' (P.isColimit (n + 1))
    (presentationAbove P n (P.index (n + 1)) (P.monotone_index (Nat.le_succ n))) (by
      have h := presentationAbove_condition P n (P.index (n + 1))
        (P.monotone_index (Nat.le_succ n))
      rw [pow_succ, mul_comm, mul_smul, Preadditive.nsmul_comp, h, smul_zero])).1

/-- The defining square of `CategoryTheory.presentationTransition`. -/
public theorem presentationTransition_fac (P : QuotientPresentation (C := C) S ℓ) (n : ℕ) :
    P.π (n + 1) ≫ presentationTransition P n =
      towerMap S (P.monotone_index (Nat.le_succ n)) ≫ P.π n :=
  (CokernelCofork.IsColimit.desc' (P.isColimit (n + 1)) _ _).2

/-- The transition map of the presented tower exhibits level `n` as the quotient of level `n + 1`
by `ℓⁿ⁺¹`. -/
public def presentationTransition_isCokernel (P : QuotientPresentation (C := C) S ℓ) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (presentationTransition P n)
      (nsmul_hom_eq_zero (ℓ ^ (n + 1)) _ (presentation_annihilated P n))) :=
  scalarQuotient_desc_isCokernel _ (P.π (n + 1)) _
    (presentationAbove_condition P n _ _) (presentationAbove_isCokernel P n _ _)
    _ (presentationTransition_fac P n)

/-- The inverse system assembled from the presented objects. -/
public abbrev presentationTower (P : QuotientPresentation (C := C) S ℓ) : ℕᵒᵖ ⥤ C :=
  { obj n := P.obj n.unop
    map := (Functor.ofOpSequence (presentationTransition P)).map
    map_id := (Functor.ofOpSequence (presentationTransition P)).map_id
    map_comp := (Functor.ofOpSequence (presentationTransition P)).map_comp }

/-- The one-step transition map of the presented tower. -/
public theorem presentationTower_map_succ (P : QuotientPresentation (C := C) S ℓ) (n : ℕ) :
    towerMap (presentationTower P) (Nat.le_succ n) = presentationTransition P n :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-- The presenting surjections are compatible with the transition maps of the two towers. -/
public theorem presentationTower_fac (P : QuotientPresentation (C := C) S ℓ) {n m : ℕ}
    (h : n ≤ m) :
    P.π m ≫ towerMap (presentationTower P) h = towerMap S (P.monotone_index h) ≫ P.π n := by
  induction m, h using Nat.le_induction with
  | base => rw [towerMap_self, towerMap_self, Category.id_comp, Category.comp_id]
  | succ m h ih =>
    rw [← towerMap_comp (presentationTower P) h (Nat.le_succ m),
      ← Category.assoc, presentationTower_map_succ, presentationTransition_fac,
      Category.assoc, ih, ← Category.assoc, towerMap_comp]

/-- The map out of the presented tower induced by a map of `S` into a tower whose levels are
killed by the successive powers of `ℓ`. -/
public def presentationMap (P : QuotientPresentation (C := C) S ℓ) (F : ℕᵒᵖ ⥤ C) (i : S ⟶ F)
    (hF : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj F n)) = 0) : presentationTower P ⟶ F :=
  NatTrans.ofOpSequence (fun n =>
    (CokernelCofork.IsColimit.desc' (P.isColimit n)
      (i.app (Opposite.op (P.index n)) ≫ towerMap F (P.le_index n))
      (nsmul_hom_eq_zero _ _ (hF n))).1) (fun n => by
    have hfac : ∀ m : ℕ, P.π m ≫ (CokernelCofork.IsColimit.desc' (P.isColimit m)
        (i.app (Opposite.op (P.index m)) ≫ towerMap F (P.le_index m))
        (nsmul_hom_eq_zero _ _ (hF m))).1 =
          i.app (Opposite.op (P.index m)) ≫ towerMap F (P.le_index m) :=
      fun m => (CokernelCofork.IsColimit.desc' (P.isColimit m) _ _).2
    simp only [presentationTower, Functor.ofOpSequence_map_homOfLE_succ]
    apply (cancel_epi (P.π (n + 1))).1
    rw [← Category.assoc, presentationTransition_fac, Category.assoc, hfac n,
      ← Category.assoc (P.π (n + 1)), hfac (n + 1),
      ← Category.assoc, i.naturality, Category.assoc, towerMap_comp,
      Category.assoc, towerMap_comp])

/-- The defining square of `CategoryTheory.presentationMap`. -/
public theorem presentationMap_fac (P : QuotientPresentation (C := C) S ℓ) (F : ℕᵒᵖ ⥤ C)
    (i : S ⟶ F) (hF : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj F n)) = 0) (n : ℕ) :
    P.π n ≫ (presentationMap P F i hF).app (Opposite.op n) =
      i.app (Opposite.op (P.index n)) ≫ towerMap F (P.le_index n) :=
  (CokernelCofork.IsColimit.desc' (P.isColimit n) _ _).2

/-- When `i` is levelwise monomorphic, the kernel of `presentationMap` at a level above the
presenting one dies under the transition map down to that level. -/
public theorem presentationMap_pro_mono (P : QuotientPresentation (C := C) S ℓ) (F : ℕᵒᵖ ⥤ C)
    (i : S ⟶ F) (hF : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj F n)) = 0)
    (hi : ∀ n, Mono (i.app (Opposite.op n))) {n m : ℕ} (h : P.index n ≤ m) :
    kernel.ι ((presentationMap P F i hF).app (Opposite.op m)) ≫
      towerMap (presentationTower P) ((P.le_index n).trans h) = 0 := by
  let x := kernel.ι ((presentationMap P F i hF).app (Opposite.op m))
  obtain ⟨A, e, he, y, hy⟩ := surjective_up_to_refinements_of_epi (P.π m) x
  dsimp only [x] at hy
  have hym : y ≫ towerMap S (P.le_index m) = 0 := by
    have := hi m
    apply (cancel_mono (i.app (Opposite.op m))).1
    rw [zero_comp, Category.assoc, i.naturality, ← presentationMap_fac P F i hF m,
      ← Category.assoc, ← hy, Category.assoc, kernel.condition, comp_zero]
  apply (cancel_epi e).1
  rw [comp_zero, ← Category.assoc, hy, Category.assoc, presentationTower_fac, ← Category.assoc]
  have ht : towerMap S (P.monotone_index ((P.le_index n).trans h)) =
      towerMap S (P.le_index m) ≫ towerMap S h := (towerMap_comp S h (P.le_index m)).symm
  rw [ht, ← Category.assoc, hym, zero_comp, zero_comp]

/-- A map into a tower which is pro-monomorphic over a tower with epimorphic transition maps,
and which is killed by that pro-monomorphism, is zero. -/
public theorem towerHom_eq_zero_of_pro_mono {A K F : ℕᵒᵖ ⥤ C} (j : K ⟶ F)
    (hA : ∀ n m (h : n ≤ m), Epi (towerMap A h))
    (hK : ∀ n, ∃ m : ℕ, ∃ h : n ≤ m,
      kernel.ι (j.app (Opposite.op m)) ≫ towerMap K h = 0)
    (a : A ⟶ K) (ha : a ≫ j = 0) : a = 0 := by
  apply NatTrans.ext
  funext n
  obtain ⟨m, h, hm⟩ := hK n.unop
  have := hA n.unop m h
  apply (cancel_epi (towerMap A h)).1
  show towerMap A h ≫ a.app n = towerMap A h ≫ 0
  rw [comp_zero, a.naturality]
  have ham : a.app (Opposite.op m) ≫ j.app (Opposite.op m) = 0 :=
    NatTrans.congr_app ha (Opposite.op m)
  rw [← kernel.lift_ι _ _ ham, Category.assoc, hm, comp_zero]

/-- The map into the presented tower induced by a map into `S` out of a tower whose transition
maps exhibit the successive quotients by the powers of `ℓ`. -/
public def presentationLift (P : QuotientPresentation (C := C) S ℓ) (A : ℕᵒᵖ ⥤ C) (l : A ⟶ S)
    (hA : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj A n)) = 0)
    (hAc : ∀ n m (h : n ≤ m), IsColimit (CokernelCofork.ofπ (towerMap A h)
      (nsmul_hom_eq_zero _ _ (hA n)))) : A ⟶ presentationTower P :=
  NatTrans.ofOpSequence (fun n =>
    (CokernelCofork.IsColimit.desc' (hAc n (P.index n) (P.le_index n))
      (l.app (Opposite.op (P.index n)) ≫ P.π n)
      (nsmul_hom_eq_zero _ _ (presentation_annihilated P n))).1) (fun n => by
    have hfac : ∀ m : ℕ, towerMap A (P.le_index m) ≫
        (CokernelCofork.IsColimit.desc' (hAc m (P.index m) (P.le_index m))
          (l.app (Opposite.op (P.index m)) ≫ P.π m)
          (nsmul_hom_eq_zero _ _ (presentation_annihilated P m))).1 =
            l.app (Opposite.op (P.index m)) ≫ P.π m :=
      fun m => (CokernelCofork.IsColimit.desc' (hAc m (P.index m) (P.le_index m)) _ _).2
    have : Epi (towerMap A (P.le_index (n + 1))) :=
      Cofork.IsColimit.epi (hAc (n + 1) (P.index (n + 1)) (P.le_index (n + 1)))
    apply (cancel_epi (towerMap A (P.le_index (n + 1)))).1
    rw [← Category.assoc, towerMap_comp,
      ← towerMap_comp A (P.le_index n) (P.monotone_index (Nat.le_succ n)),
      Category.assoc, hfac n,
      ← Category.assoc (towerMap A (P.le_index (n + 1))), hfac (n + 1),
      ← Category.assoc, l.naturality, Category.assoc, ← presentationTower_fac,
      Category.assoc])

/-- The defining square of `CategoryTheory.presentationLift`. -/
public theorem presentationLift_fac (P : QuotientPresentation (C := C) S ℓ) (A : ℕᵒᵖ ⥤ C)
    (l : A ⟶ S) (hA : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj A n)) = 0)
    (hAc : ∀ n m (h : n ≤ m), IsColimit (CokernelCofork.ofπ (towerMap A h)
      (nsmul_hom_eq_zero _ _ (hA n)))) (n : ℕ) :
    towerMap A (P.le_index n) ≫ (presentationLift P A l hA hAc).app (Opposite.op n) =
      l.app (Opposite.op (P.index n)) ≫ P.π n :=
  (CokernelCofork.IsColimit.desc' (hAc n (P.index n) (P.le_index n)) _ _).2

/-- The lift into the presented tower followed by the map out of it is the composite of the two
maps it was built from. -/
public theorem presentationLift_map (P : QuotientPresentation (C := C) S ℓ) (A F : ℕᵒᵖ ⥤ C)
    (l : A ⟶ S) (i : S ⟶ F) (hA : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj A n)) = 0)
    (hAc : ∀ n m (h : n ≤ m), IsColimit (CokernelCofork.ofπ (towerMap A h)
      (nsmul_hom_eq_zero _ _ (hA n))))
    (hF : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj F n)) = 0) :
    presentationLift P A l hA hAc ≫ presentationMap P F i hF = l ≫ i := by
  apply NatTrans.ext
  funext n
  have : Epi (towerMap A (P.le_index n.unop)) :=
    Cofork.IsColimit.epi (hAc n.unop (P.index n.unop) (P.le_index n.unop))
  apply (cancel_epi (towerMap A (P.le_index n.unop))).1
  show towerMap A (P.le_index n.unop) ≫
    ((presentationLift P A l hA hAc).app n ≫ (presentationMap P F i hF).app n) =
    towerMap A (P.le_index n.unop) ≫ (l.app n ≫ i.app n)
  rw [← Category.assoc, presentationLift_fac, Category.assoc, presentationMap_fac,
    ← i.naturality, ← Category.assoc, ← l.naturality, Category.assoc]

/-- The map out of the presented tower is killed by anything killing the map it came from. -/
public theorem presentationMap_comp_eq_zero (P : QuotientPresentation (C := C) S ℓ)
    (F G : ℕᵒᵖ ⥤ C) (i : S ⟶ F) (f : F ⟶ G)
    (hF : ∀ n, ℓ ^ (n + 1) • (𝟙 (towerObj F n)) = 0) (hi : i ≫ f = 0) :
    presentationMap P F i hF ≫ f = 0 := by
  apply NatTrans.ext
  funext n
  apply (cancel_epi (P.π n.unop)).1
  show P.π n.unop ≫ ((presentationMap P F i hF).app n ≫ f.app n) = P.π n.unop ≫ 0
  rw [comp_zero, ← Category.assoc, presentationMap_fac, Category.assoc, f.naturality,
    ← Category.assoc]
  have h := NatTrans.congr_app hi (Opposite.op (P.index n.unop))
  change i.app (Opposite.op (P.index n.unop)) ≫ f.app (Opposite.op (P.index n.unop)) = 0 at h
  rw [h, zero_comp]

end TowerNormalization

end CategoryTheory

end
