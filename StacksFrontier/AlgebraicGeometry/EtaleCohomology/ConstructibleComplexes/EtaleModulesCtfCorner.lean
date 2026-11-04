module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfCentralIdempotent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.MainstreamTransport

/-!
# The summand of `D_ctf` cut out by a central idempotent, over the corner ring

Let `Λ` be a ring and `e ∈ Λ` a central idempotent. The corner `eΛ` is a ring with unit `e`
(`IsIdempotentElem.Corner`), and `λ ↦ eλ` is a surjective ring homomorphism `Λ → eΛ`. A
`Λ`-module `M` gives the `eΛ`-module `eM`; here it is realized as the coextension of scalars
`Hom_Λ(eΛ, M)`, which is both a right adjoint and (the homomorphism being surjective with
central idempotent kernel generator) a left adjoint of restriction of scalars. Applied
sectionwise it is an exact functor from sheaves of `Λ`-modules to sheaves of `eΛ`-modules on
any site, whose composite with restriction of scalars is the summand `eF` of
`CategoryTheory.idempotentPart`.

It keeps constructible flat sheaves constructible flat, now as sheaves of `eΛ`-modules, and keeps
`D_ctf`. For a complete family of orthogonal central idempotents every complex of sheaves of
`Λ`-modules is, naturally, the direct sum of its parts. For a finite ring `Λ` the primary
idempotents of `Stacks.EtaleCohomology.exists_primary_completeOrthogonalIdempotents` give such a
family, with `ℓ^a` killing the corner `e_ℓ Λ`: this is the reduction of [Stacks, Tag 03UG],
Step 3, to coefficient rings killed by a power of a prime.

## Main definitions

* `Stacks.EtaleCohomology.cornerRingHom` — the ring homomorphism `λ ↦ eλ` onto the corner.
* `Stacks.EtaleCohomology.sheafCorner` — the sheaf of `eΛ`-modules `eF`.

## Main results

* `Stacks.EtaleCohomology.sheafCornerRestrictIso` — `eF`, viewed as a sheaf of `Λ`-modules, is
  the summand `CategoryTheory.idempotentPart` of multiplication by `e`.
* `Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule.corner` — `eF` is constructible flat
  over `eΛ` when `F` is constructible flat over `Λ`.
* `Stacks.EtaleCohomology.IsCtf.corner` — the complex `eC` lies in `D_ctf(X, eΛ)` when `C` lies
  in `D_ctf(X, Λ)`.
* `Stacks.EtaleCohomology.cornerDecompositionIso` — a complete family of orthogonal central
  idempotents `e_i` splits every complex `C` of sheaves of `Λ`-modules as `⨁ e_i C`, naturally.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w r

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {p : 𝟭 C ⟶ 𝟭 C}

/-- A morphism killed by `𝟙 - p` factors through the summand cut out by `p`. -/
def idempotentPartLift {X A : C} (f : X ⟶ A) (hf : f ≫ (𝟙 A - p.app' A) = 0) :
    X ⟶ (idempotentPart p).obj A :=
  kernel.lift _ f hf

/-- The lift `idempotentPartLift f hf` composed with the inclusion of the summand is `f`. -/
theorem idempotentPartLift_ι {X A : C} (f : X ⟶ A) (hf : f ≫ (𝟙 A - p.app' A) = 0) :
    idempotentPartLift f hf ≫ (idempotentPartι p).app A = f :=
  kernel.lift_ι _ _ _

section Retract

variable {P : C ⥤ C} (i : P ⟶ 𝟭 C) (π : 𝟭 C ⟶ P) (hiπ : i ≫ π = 𝟙 P) (hπi : π ≫ i = p)

include hiπ hπi in
/-- If `i ≫ π = 𝟙` and `π ≫ i = p`, then `i` is killed by `𝟙 - p`. -/
theorem retract_comp_sub (A : C) : i.app A ≫ (𝟙 A - p.app' A) = 0 := by
  have h1 : i.app A ≫ π.app A = 𝟙 _ := NatTrans.congr_app hiπ A
  have h2 : π.app A ≫ i.app A = p.app' A := NatTrans.congr_app hπi A
  have h3 : i.app A ≫ p.app' A = i.app A := by
    rw [← h2, ← Category.assoc, h1, Category.id_comp]
  rw [Preadditive.comp_sub, h3]
  exact sub_eq_zero.2 (Category.comp_id _)

/-- The comparison from a retract of the identity to the summand of its idempotent. -/
def idempotentPartOfRetract : P ⟶ idempotentPart p where
  app A := idempotentPartLift (i.app A) (retract_comp_sub i π hiπ hπi A)
  naturality A B f := by
    refine (cancel_mono ((idempotentPartι p).app B)).1 ?_
    rw [Category.assoc, idempotentPartLift_ι, Category.assoc, idempotentPart_map_ι,
      ← Category.assoc, idempotentPartLift_ι]
    exact i.naturality f

/-- The comparison `idempotentPartOfRetract` composed with the inclusion of the summand is `i`. -/
theorem idempotentPartOfRetract_ι (A : C) :
    (idempotentPartOfRetract i π hiπ hπi).app A ≫ (idempotentPartι p).app A = i.app A :=
  idempotentPartLift_ι _ _

/-- **A retract of the identity functor is the summand of its idempotent.** If `i ≫ π = 𝟙` and
`π ≫ i = p`, the functor `P` is the summand `CategoryTheory.idempotentPart p`. -/
def idempotentPartIsoOfRetract : P ≅ idempotentPart p where
  hom := idempotentPartOfRetract i π hiπ hπi
  inv := idempotentPartι p ≫ π
  hom_inv_id := by
    ext A
    simp only [NatTrans.comp_app, NatTrans.id_app]
    rw [← Category.assoc, idempotentPartOfRetract_ι]
    exact congrArg (fun t => t.app A) hiπ
  inv_hom_id := by
    ext A
    simp only [NatTrans.comp_app, NatTrans.id_app]
    refine (cancel_mono ((idempotentPartι p).app A)).1 ?_
    rw [Category.assoc, Category.assoc, idempotentPartOfRetract_ι, Category.id_comp,
      show π.app A ≫ i.app A = p.app A from congrArg (fun t => t.app A) hπi]
    exact idempotentPartι_comp_app A

end Retract

/-- An endomorphism of the identity functor acts degreewise on homological complexes. -/
def homologicalComplexEndo {ι : Type*} (c : ComplexShape ι) (q : 𝟭 C ⟶ 𝟭 C) :
    𝟭 (HomologicalComplex C c) ⟶ 𝟭 _ where
  app K :=
    { f := fun n => q.app (K.X n)
      comm' := fun i j _ => (q.naturality (K.d i j)).symm }
  naturality K L f := by
    ext n
    exact q.naturality (f.f n)

end CategoryTheory

namespace Stacks.EtaleCohomology

section Ring

variable {Λ : Type r} [Ring Λ] {e : Λ} (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a)

include he hc in
/-- For a central idempotent `e`, `e a e = e a`. -/
theorem mul_mul_eq_of_central (a : Λ) : e * a * e = e * a := by
  rw [mul_assoc, hc, ← mul_assoc, he.eq]

/-- The idempotent `e` acts as the identity on the left of its corner. -/
theorem mul_corner (s : he.Corner) : e * s.1 = s.1 :=
  ((Subsemigroup.mem_corner_iff he).1 s.2).1

/-- The idempotent `e` acts as the identity on the right of its corner. -/
theorem corner_mul (s : he.Corner) : s.1 * e = s.1 :=
  ((Subsemigroup.mem_corner_iff he).1 s.2).2

include hc in
/-- **The ring homomorphism onto the corner** of a central idempotent: `λ ↦ eλ = eλe`. -/
def cornerRingHom : Λ →+* he.Corner where
  toFun a := ⟨e * a * e, a, rfl⟩
  map_one' := Subtype.ext (show e * 1 * e = e by rw [mul_one, he.eq])
  map_mul' a b := Subtype.ext (show e * (a * b) * e = e * a * e * (e * b * e) by
    rw [mul_mul_eq_of_central he hc, mul_mul_eq_of_central he hc, mul_mul_eq_of_central he hc,
      ← mul_assoc (e * a) e b, mul_mul_eq_of_central he hc, mul_assoc])
  map_zero' := Subtype.ext (show e * 0 * e = 0 by rw [mul_zero, zero_mul])
  map_add' a b := Subtype.ext (show e * (a + b) * e = e * a * e + e * b * e by
    rw [mul_add, add_mul])

/-- The underlying element of `cornerRingHom he hc a` is `e a`. -/
theorem cornerRingHom_val (a : Λ) : (cornerRingHom he hc a).1 = e * a :=
  mul_mul_eq_of_central he hc a

/-- `cornerRingHom` is the identity on elements of the corner. -/
theorem cornerRingHom_corner (s : he.Corner) : cornerRingHom he hc s.1 = s :=
  Subtype.ext (show e * s.1 * e = s.1 by rw [mul_corner, corner_mul])

/-- The ring homomorphism onto the corner is surjective. -/
theorem cornerRingHom_surjective : Function.Surjective (cornerRingHom he hc) :=
  fun s => ⟨s.1, cornerRingHom_corner he hc s⟩

/-- The corner of a finite ring is finite. -/
instance corner_finite [Finite Λ] : Finite he.Corner :=
  Finite.of_injective (fun s : he.Corner => s.1) Subtype.val_injective

include hc in
/-- An integer killing `eΛ` is zero in the corner: for the primary idempotent `e_ℓ` of a finite
ring, `ℓ ^ a = 0` in `e_ℓ Λ`. -/
theorem natCast_corner_eq_zero (n : ℕ) (h : (n : Λ) * e = 0) : (n : he.Corner) = 0 := by
  rw [← map_natCast (cornerRingHom he hc) n]
  exact Subtype.ext ((cornerRingHom_val he hc n).trans
    (((Nat.cast_commute n e).eq.symm).trans h))

/-- `cornerRingHom` sends `e` to the unit `1` of the corner. -/
theorem cornerRingHom_idem : cornerRingHom he hc e = 1 :=
  Subtype.ext (show e * e * e = e by rw [he.eq, he.eq])

/-- A module over the target of a surjective ring homomorphism which is finite over the source is
finite over the target. -/
theorem _root_.ModuleCat.finite_of_finite_restrictScalars {R : Type*} {S : Type*} [Ring R]
    [Ring S] (f : R →+* S) (N : ModuleCat.{v} S)
    [h : Module.Finite R ((ModuleCat.restrictScalars f).obj N)] : Module.Finite S N := by
  let N' := (ModuleCat.restrictScalars f).obj N
  obtain ⟨s, hs⟩ : ∃ s : Finset N', Submodule.span R (s : Set N') = ⊤ := h.fg_top
  let t : Finset N := s
  let φ : N' → N := id
  have key : ∀ y ∈ Submodule.span R (s : Set N'), φ y ∈ Submodule.span S (t : Set N) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact (Submodule.span S (t : Set N)).zero_mem
    | add y z _ _ hy hz => exact (Submodule.span S (t : Set N)).add_mem hy hz
    | smul a y _ hy => exact (Submodule.span S (t : Set N)).smul_mem (f a) hy
  refine ⟨⟨t, eq_top_iff.2 fun x _ => key x ?_⟩⟩
  rw [hs]
  trivial

/-- The part `eM = {m | e m = m}` of a `Λ`-module `M` fixed by the central idempotent `e`. -/
def cornerSubmodule (M : Type*) [AddCommGroup M] [Module Λ M] : Submodule Λ M where
  carrier := {m | e • m = m}
  add_mem' {a b} ha hb := by
    change e • (a + b) = a + b
    rw [smul_add, show e • a = a from ha, show e • b = b from hb]
  zero_mem' := smul_zero e
  smul_mem' a {m} hm := by
    change e • a • m = a • m
    rw [smul_smul, ← hc a, mul_smul, show e • m = m from hm]

/-- The fixed part `eM` is a module over the corner `eΛ`. -/
instance cornerSubmodule.module (M : Type*) [AddCommGroup M] [Module Λ M] :
    Module he.Corner (cornerSubmodule hc M) where
  smul s m := ⟨s.1 • m.1, show e • s.1 • m.1 = s.1 • m.1 by rw [smul_smul, mul_corner he]⟩
  one_smul m := Subtype.ext m.2
  mul_smul s t m := Subtype.ext (mul_smul s.1 t.1 m.1)
  smul_zero s := Subtype.ext (smul_zero s.1)
  smul_add s m n := Subtype.ext (smul_add s.1 m.1 n.1)
  add_smul s t m := Subtype.ext (add_smul s.1 t.1 m.1)
  zero_smul m := Subtype.ext (zero_smul Λ m.1)

/-- The action of the corner on `eM` is the action of its underlying element of `Λ`. -/
theorem cornerSubmodule.smul_val {M : Type*} [AddCommGroup M] [Module Λ M] (s : he.Corner)
    (m : cornerSubmodule hc M) : (s • m).1 = s.1 • m.1 :=
  rfl

/-- **The `eΛ`-module `eM`** of a `Λ`-module `M`, functorially. -/
def cornerModule : ModuleCat.{v} Λ ⥤ ModuleCat.{v} he.Corner where
  obj M := ModuleCat.of he.Corner (cornerSubmodule hc M)
  map {M N} f := ModuleCat.ofHom
    { toFun := fun m => ⟨f m.1, show e • f m.1 = f m.1 by
        rw [← LinearMap.map_smul, show e • m.1 = m.1 from m.2]⟩
      map_add' := fun m n => Subtype.ext (map_add f.hom m.1 n.1)
      map_smul' := fun s m => Subtype.ext (f.hom.map_smul s.1 m.1) }

/-- Restriction of scalars from the corner `eΛ` to `Λ`, along
`Stacks.EtaleCohomology.cornerRingHom`: an `eΛ`-module is a `Λ`-module on which `e` acts as the
identity. -/
def cornerRestrict : ModuleCat.{v} he.Corner ⥤ ModuleCat.{v} Λ :=
  ModuleCat.restrictScalars.{v} (cornerRingHom he hc)

/-- The inclusion `eM ⟶ M`, as `Λ`-modules. -/
def cornerModuleι : cornerModule.{v} he hc ⋙ cornerRestrict.{v} he hc ⟶ 𝟭 _ where
  app M := ModuleCat.ofHom (X := (cornerRestrict he hc).obj ((cornerModule he hc).obj M)) (Y := M)
    { toFun := fun m => (m : cornerSubmodule hc M).1
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        change (cornerRingHom he hc a).1 • (m : cornerSubmodule hc M).1 =
          a • (m : cornerSubmodule hc M).1
        rw [cornerRingHom_val, ← hc a, mul_smul, show e • (m : cornerSubmodule hc M).1 =
          (m : cornerSubmodule hc M).1 from (m : cornerSubmodule hc M).2] }
  naturality _ _ _ := rfl

/-- The projection `M ⟶ eM`, `m ↦ e m`, as `Λ`-modules. -/
def cornerModuleπ : 𝟭 _ ⟶ cornerModule.{v} he hc ⋙ cornerRestrict.{v} he hc where
  app M := ModuleCat.ofHom (X := M) (Y := (cornerRestrict he hc).obj ((cornerModule he hc).obj M))
    { toFun := fun m => (⟨e • m, show e • e • m = e • m by rw [smul_smul, he.eq]⟩ :
        cornerSubmodule hc M)
      map_add' := fun m n => Subtype.ext (smul_add e m n)
      map_smul' := fun a m => Subtype.ext (show e • a • m = (cornerRingHom he hc a).1 • e • m by
        rw [cornerRingHom_val, smul_smul, smul_smul, mul_mul_eq_of_central he hc]) }
  naturality M N f := by
    ext m
    exact Subtype.ext (f.hom.map_smul e m).symm

/-- The counit `eN ⟶ N` for an `eΛ`-module `N`. -/
def cornerModuleCounit : cornerRestrict.{v} he hc ⋙ cornerModule.{v} he hc ⟶ 𝟭 _ where
  app N := ModuleCat.ofHom (X := (cornerModule he hc).obj ((cornerRestrict he hc).obj N)) (Y := N)
    { toFun := fun m => (m : cornerSubmodule hc ((cornerRestrict he hc).obj N)).1
      map_add' := fun _ _ => rfl
      map_smul' := fun s m => by
        change cornerRingHom he hc s.1 • @id N m.1 = s • @id N m.1
        rw [cornerRingHom_corner] }
  naturality _ _ _ := rfl

/-- The unit `N ⟶ eN` for an `eΛ`-module `N`: `e` acts on `N` as the identity. -/
def cornerModuleUnit : 𝟭 _ ⟶ cornerRestrict.{v} he hc ⋙ cornerModule.{v} he hc where
  app N := ModuleCat.ofHom (X := N) (Y := (cornerModule he hc).obj ((cornerRestrict he hc).obj N))
    { toFun := fun n => (⟨n, show cornerRingHom he hc e • (n : N) = n by
        rw [cornerRingHom_idem, one_smul]⟩ : cornerSubmodule hc ((cornerRestrict he hc).obj N))
      map_add' := fun _ _ => rfl
      map_smul' := fun s n => Subtype.ext (show s • n = cornerRingHom he hc s.1 • n by
        rw [cornerRingHom_corner]) }
  naturality _ _ _ := rfl

/-- **`M ↦ eM` is left adjoint to restriction of scalars** from the corner. -/
def cornerAdj : cornerModule.{v} he hc ⊣ cornerRestrict.{v} he hc :=
  Adjunction.mkOfUnitCounit
    { unit := cornerModuleπ he hc
      counit := cornerModuleCounit he hc
      left_triangle := by
        ext M m
        exact Subtype.ext m.2
      right_triangle := by
        ext N n
        change cornerRingHom he hc e • @id N n = n
        rw [cornerRingHom_idem, one_smul]
        rfl }

/-- **Restriction of scalars from the corner is left adjoint to `M ↦ eM`.** -/
def cornerRestrictAdj : cornerRestrict.{v} he hc ⊣ cornerModule.{v} he hc :=
  Adjunction.mkOfUnitCounit
    { unit := cornerModuleUnit he hc
      counit := cornerModuleι he hc
      left_triangle := by
        ext N n
        rfl
      right_triangle := by
        ext M m
        rfl }

/-- The inclusion `eM ⟶ M` followed by the projection `M ⟶ eM` is the identity. -/
theorem cornerModuleι_π : cornerModuleι.{v} he hc ≫ cornerModuleπ.{v} he hc = 𝟙 _ := by
  ext M m
  exact Subtype.ext m.2

/-- The projection `M ⟶ eM` followed by the inclusion `eM ⟶ M` is multiplication by `e`. -/
theorem cornerModuleπ_ι :
    cornerModuleπ.{v} he hc ≫ cornerModuleι.{v} he hc = moduleCatCentralEndo e hc := by
  ext M m
  rfl

/-- `M ↦ eM` is a left adjoint. -/
instance cornerModule_isLeftAdjoint : (cornerModule.{v} he hc).IsLeftAdjoint :=
  (cornerAdj he hc).isLeftAdjoint

/-- `M ↦ eM` is a right adjoint. -/
instance cornerModule_isRightAdjoint : (cornerModule.{v} he hc).IsRightAdjoint :=
  (cornerRestrictAdj he hc).isRightAdjoint

/-- Restriction of scalars from the corner is a right adjoint. -/
instance cornerRestrict_isRightAdjoint : (cornerRestrict.{v} he hc).IsRightAdjoint :=
  (cornerAdj he hc).isRightAdjoint

/-- Restriction of scalars from the corner is a left adjoint. -/
instance cornerRestrict_isLeftAdjoint : (cornerRestrict.{v} he hc).IsLeftAdjoint :=
  (cornerRestrictAdj he hc).isLeftAdjoint

include hc in
/-- `eM` is finite projective over `eΛ` when `M` is finite projective over `Λ`. -/
theorem cornerModule_finite_projective (E : ModuleCat.{v} Λ) [hfin : Module.Finite Λ E]
    [hproj : Module.Projective Λ E] [Small.{v} Λ] :
    Module.Finite he.Corner ((cornerModule.{v} he hc).obj E) ∧
      Module.Projective he.Corner ((cornerModule.{v} he hc).obj E) := by
  constructor
  · have hsurj : Function.Surjective ((cornerModuleπ.{v} he hc).app E).hom := fun m =>
      ⟨((cornerModuleι.{v} he hc).app E).hom m,
        congrArg (fun t => (t.app E).hom m) (cornerModuleι_π.{v} he hc)⟩
    have : Module.Finite Λ ((𝟭 (ModuleCat.{v} Λ)).obj E) := hfin
    have : Module.Finite Λ ((cornerModule.{v} he hc ⋙ cornerRestrict.{v} he hc).obj E) :=
      Module.Finite.of_surjective _ hsurj
    have : Module.Finite Λ ((ModuleCat.restrictScalars (cornerRingHom he hc)).obj
      ((cornerModule.{v} he hc).obj E)) := this
    exact ModuleCat.finite_of_finite_restrictScalars (cornerRingHom he hc) _
  · have : Small.{v} he.Corner := small_of_injective (f := fun s : he.Corner => s.1)
      Subtype.val_injective
    have hE : Projective E := (IsProjective.iff_projective E).1 hproj
    have := Functor.preservesEpimorphisms_of_adjunction (cornerRestrictAdj.{v} he hc)
    exact (IsProjective.iff_projective _).2 ((cornerAdj.{v} he hc).map_projective E hE)

end Ring

section Sheaf

universe u₁ v₁

variable {Λ : Type r} [Ring Λ] {e : Λ} (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a)
  {D : Type u₁} [Category.{v₁} D] (J : GrothendieckTopology D)

/-- `M ↦ eM` takes sheaves to sheaves. -/
instance cornerModule_hasSheafCompose : J.HasSheafCompose (cornerModule.{v} he hc) :=
  inferInstance

/-- Restriction of scalars from the corner takes sheaves to sheaves. -/
instance cornerRestrict_hasSheafCompose : J.HasSheafCompose (cornerRestrict.{v} he hc) :=
  inferInstance

/-- **The sheaf of `eΛ`-modules `eF`** of a sheaf of `Λ`-modules `F`, for a central idempotent
`e`: `M ↦ eM` applied sectionwise. -/
abbrev sheafCorner : Sheaf J (ModuleCat.{v} Λ) ⥤ Sheaf J (ModuleCat.{v} he.Corner) :=
  sheafCompose J (cornerModule.{v} he hc)

/-- Restriction of scalars from `eΛ` to `Λ`, sectionwise. -/
abbrev sheafCornerRestrict : Sheaf J (ModuleCat.{v} he.Corner) ⥤ Sheaf J (ModuleCat.{v} Λ) :=
  sheafCompose J (cornerRestrict.{v} he hc)

/-- `F ↦ eF` is left adjoint to restriction of scalars. -/
def sheafCornerAdj : sheafCorner.{v} he hc J ⊣ sheafCornerRestrict.{v} he hc J :=
  SmallEtale.sheafComposeAdjunction J (cornerAdj.{v} he hc)

/-- Restriction of scalars is left adjoint to `F ↦ eF`. -/
def sheafCornerRestrictAdj : sheafCornerRestrict.{v} he hc J ⊣ sheafCorner.{v} he hc J :=
  SmallEtale.sheafComposeAdjunction J (cornerRestrictAdj.{v} he hc)

/-- `F ↦ eF` is a left adjoint. -/
instance sheafCorner_isLeftAdjoint : (sheafCorner.{v} he hc J).IsLeftAdjoint :=
  (sheafCornerAdj he hc J).isLeftAdjoint

/-- `F ↦ eF` is a right adjoint. -/
instance sheafCorner_isRightAdjoint : (sheafCorner.{v} he hc J).IsRightAdjoint :=
  (sheafCornerRestrictAdj he hc J).isRightAdjoint

/-- `F ↦ eF` is additive. -/
instance sheafCorner_additive : (sheafCorner.{v} he hc J).Additive where
  map_add := by
    intros
    ext U m
    rfl

/-- Restriction of scalars from the corner, on sheaves, is additive. -/
instance sheafCornerRestrict_additive : (sheafCornerRestrict.{v} he hc J).Additive where
  map_add := by
    intros
    ext U m
    rfl

/-- The inclusion `eF ⟶ F`, as sheaves of `Λ`-modules. -/
def sheafCornerι : sheafCorner.{v} he hc J ⋙ sheafCornerRestrict.{v} he hc J ⟶ 𝟭 _ where
  app F := ⟨Functor.whiskerLeft F.obj (cornerModuleι.{v} he hc)⟩
  naturality _ _ f := by
    ext U m
    rfl

/-- The projection `F ⟶ eF`, `m ↦ e m`, as sheaves of `Λ`-modules. -/
def sheafCornerπ : 𝟭 _ ⟶ sheafCorner.{v} he hc J ⋙ sheafCornerRestrict.{v} he hc J where
  app F := ⟨Functor.whiskerLeft F.obj (cornerModuleπ.{v} he hc)⟩
  naturality _ _ f := by
    ext U m
    exact Subtype.ext ((f.hom.app U).hom.map_smul e m).symm

/-- The inclusion `eF ⟶ F` followed by the projection `F ⟶ eF` is the identity. -/
theorem sheafCornerι_π : sheafCornerι.{v} he hc J ≫ sheafCornerπ.{v} he hc J = 𝟙 _ := by
  ext F U m
  exact Subtype.ext m.2

/-- The projection `F ⟶ eF` followed by the inclusion `eF ⟶ F` is multiplication by `e`. -/
theorem sheafCornerπ_ι :
    sheafCornerπ.{v} he hc J ≫ sheafCornerι.{v} he hc J = sheafCentralEndo e hc J := by
  ext F U m
  rfl

/-- **`eF`, as a sheaf of `Λ`-modules, is the summand of `F` cut out by multiplication by
`e`.** -/
def sheafCornerRestrictIso [HasSheafify J (ModuleCat.{v} Λ)] :
    sheafCorner.{v} he hc J ⋙ sheafCornerRestrict.{v} he hc J ≅
      idempotentPart (sheafCentralEndo e hc J) :=
  idempotentPartIsoOfRetract _ _ (sheafCornerι_π he hc J) (sheafCornerπ_ι he hc J)

variable {D' : Type*} [Category* D'] {K : GrothendieckTopology D'} (G : D ⥤ D')
  [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous (ModuleCat.{v} Λ) J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous (ModuleCat.{v} he.Corner) J K).IsRightAdjoint]

/-- **`F ↦ eF` commutes with pullback of sheaves**: both composites are left adjoint to the same
functor, restriction of scalars commuting with pushforward on the nose. -/
def sheafCornerPullbackIso :
    G.sheafPullback (ModuleCat.{v} Λ) J K ⋙ sheafCorner.{v} he hc K ≅
      sheafCorner.{v} he hc J ⋙ G.sheafPullback (ModuleCat.{v} he.Corner) J K :=
  Adjunction.leftAdjointUniq
    ((G.sheafAdjunctionContinuous _ J K).comp (sheafCornerAdj.{v} he hc K))
    (((sheafCornerAdj.{v} he hc J).comp (G.sheafAdjunctionContinuous _ J K)).ofNatIsoRight
      (Iso.refl _))

end Sheaf

section ConstructibleFlat

open Stacks.ConstantSheaf

universe u₁ v₁

variable {Λ : Type r} [Ring Λ] {e : Λ} (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a)

/-- `eF` is locally constant with finite projective values over `eΛ` when `F` is so over `Λ`. -/
theorem isFiniteProjectiveLocallyConstant_sheafCorner {D : Type u₁} [Category.{v₁} D]
    (J : GrothendieckTopology D) [Small.{v} Λ]
    [∀ V : D, HasWeakSheafify (J.over V) (ModuleCat.{v} Λ)]
    [∀ V : D, HasWeakSheafify (J.over V) (ModuleCat.{v} he.Corner)]
    {F : Sheaf J (ModuleCat.{v} Λ)} (hF : IsFiniteProjectiveLocallyConstant Λ J F) :
    IsFiniteProjectiveLocallyConstant he.Corner J ((sheafCorner.{v} he hc J).obj F) := by
  intro U
  obtain ⟨I, V, f, hcov, hloc⟩ := hF U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, hfin, hproj, ⟨eE⟩⟩ := hloc i
  obtain ⟨hfin', hproj'⟩ := cornerModule_finite_projective.{v} he hc E
  have : (J.over (V i)).PreservesSheafification (cornerModule.{v} he hc) :=
    have := (cornerAdj.{v} he hc).isLeftAdjoint
    inferInstance
  let e₁ : (constantSheaf (J.over (V i)) (ModuleCat.{v} he.Corner)).obj
      ((cornerModule.{v} he hc).obj E) ≅
      (sheafCorner.{v} he hc (J.over (V i))).obj
        ((constantSheaf (J.over (V i)) (ModuleCat.{v} Λ)).obj E) :=
    (constantCommuteCompose (J.over (V i)) (cornerModule.{v} he hc)).symm.app E
  let e₂ : (sheafCorner.{v} he hc (J.over (V i))).obj
        ((J.overPullback (ModuleCat.{v} Λ) (V i)).obj F) ≅
      (J.overPullback (ModuleCat.{v} he.Corner) (V i)).obj ((sheafCorner.{v} he hc J).obj F) :=
    Iso.refl _
  exact ⟨(cornerModule.{v} he hc).obj E, hfin', hproj',
    ⟨e₁ ≪≫ (sheafCorner.{v} he hc (J.over (V i))).mapIso eE ≪≫ e₂⟩⟩

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **`eF` is constructible flat over `eΛ`** when `F` is constructible flat over `Λ`, on the small
étale site of Stacks 021B: the same stratification works. -/
theorem isConstructibleFlatModuleSheaf_sheafCorner (B : BigEtaleSite.{u}) (X : B.Scheme)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (hF : IsConstructibleFlatModuleSheaf.{u, max (u + 1) r, r} B X Λ F) :
    IsConstructibleFlatModuleSheaf.{u, max (u + 1) r, r} B X he.Corner
      ((sheafCorner he hc _).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  have : Small.{max (u + 1) r} Λ := small_max.{u + 1} Λ
  exact isFiniteProjectiveLocallyConstant_congr he.Corner _
    ((sheafCornerPullbackIso he hc _
      (AlgebraicGeometry.smallEtaleBaseChange B (s.inclusion i))).app F)
    (isFiniteProjectiveLocallyConstant_sheafCorner he hc _ (hs i))

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- **`eF` is constructible flat over `eΛ`** when `F` is constructible flat over `Λ`, on Mathlib's
small étale site. -/
theorem IsConstructibleFlatEtaleModule.corner {B : BigEtaleSite.{u}} {X : B.Scheme}
    {F : EtaleModules.{u, r} Λ X.obj} (hF : IsConstructibleFlatEtaleModule B X Λ F) :
    IsConstructibleFlatEtaleModule B X he.Corner
      ((sheafCorner he hc X.obj.smallEtaleTopology).obj F) :=
  isConstructibleFlatModuleSheaf_sheafCorner he hc B X hF

/-- **`eC` lies in `D_ctf(X, eΛ)`** when the complex `C` of sheaves of `Λ`-modules lies in
`D_ctf(X, Λ)`, for a central idempotent `e` of `Λ`: `F ↦ eF` is exact, commutes with inverse
images and keeps constructible flat sheaves constructible flat. -/
theorem IsCtf.corner {B : BigEtaleSite.{u}} {X : B.Scheme}
    {C : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ}
    (hC : IsCtf B X Λ (DerivedCategory.Q.obj C)) :
    IsCtf B X he.Corner (DerivedCategory.Q.obj
      (((sheafCorner he hc X.obj.smallEtaleTopology).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)) := by
  intro W f hW hW'
  let g := B.inclusion.map f
  have h := (hC W f hW hW').of_iso B W Λ
    ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.app C)
  have h' := IsRepresentedByConstructibleFlatEtaleComplex.map B Λ
    (sheafCorner he hc W.obj.smallEtaleTopology) (fun G hG => hG.corner he hc) h
  have : ((smallEtaleBaseChange g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      X.obj.smallEtaleTopology W.obj.smallEtaleTopology).IsRightAdjoint :=
    (etaleModuleInverseImageAdj.{u, r} Λ g).isRightAdjoint
  have : ((smallEtaleBaseChange g).sheafPushforwardContinuous
      (ModuleCat.{max (u + 1) r} he.Corner)
      X.obj.smallEtaleTopology W.obj.smallEtaleTopology).IsRightAdjoint :=
    (etaleModuleInverseImageAdj.{u, r} he.Corner g).isRightAdjoint
  let η := sheafCornerPullbackIso he hc X.obj.smallEtaleTopology (K := W.obj.smallEtaleTopology)
    (smallEtaleBaseChange g)
  exact h'.of_iso B W he.Corner (DerivedCategory.Q.mapIso
    (HomologicalComplex.Hom.isoOfComponents (fun n => η.app (C.X n))
      (fun i j _ => (η.hom.naturality (C.d i j)).symm)) ≪≫
    ((etaleModuleInverseImage.{u, r} he.Corner g).mapDerivedCategoryFactors.app _).symm)

end ConstructibleFlat

section Decomposition

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ : Type r} [Ring Λ] {D : Type*} [Category* D] (J : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{v} Λ)]
  {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → Λ} (he : CompleteOrthogonalIdempotents e)
  (hc : ∀ i (a : Λ), a * e i = e i * a)
  {ι' : Type*} (c : ComplexShape ι')

/-- The degreewise idempotents of a complete family of orthogonal central idempotents, on
complexes of sheaves of `Λ`-modules. -/
abbrev cornerComplexEndo (i : ι) :
    𝟭 (HomologicalComplex (Sheaf J (ModuleCat.{v} Λ)) c) ⟶ 𝟭 _ :=
  homologicalComplexEndo c (sheafCentralEndo (e i) (hc i) J)

/-- The summand `e_i C` of a complex `C` of sheaves of `Λ`-modules, as a complex of sheaves of
`Λ`-modules: `F ↦ e_i F` degreewise. -/
abbrev cornerComplexPart (i : ι) :
    HomologicalComplex (Sheaf J (ModuleCat.{v} Λ)) c ⥤
      HomologicalComplex (Sheaf J (ModuleCat.{v} Λ)) c :=
  (sheafCorner.{v} (he.idem i) (hc i) J ⋙ sheafCornerRestrict.{v} (he.idem i) (hc i) J
    ).mapHomologicalComplex c

/-- The summand `e_i C`, as the summand cut out by the degreewise idempotent. -/
def cornerComplexPartIso (i : ι) :
    cornerComplexPart.{v} J he hc c i ≅ idempotentPart (cornerComplexEndo.{v} J hc c i) :=
  idempotentPartIsoOfRetract
    (NatTrans.mapHomologicalComplex (sheafCornerι.{v} (he.idem i) (hc i) J) c ≫
      (Functor.mapHomologicalComplexIdIso _ c).hom)
    ((Functor.mapHomologicalComplexIdIso _ c).inv ≫
      NatTrans.mapHomologicalComplex (sheafCornerπ.{v} (he.idem i) (hc i) J) c)
    (by
      ext K n U m
      exact Subtype.ext m.2)
    (by
      ext K n U m
      rfl)

omit [DecidableEq ι] in
include he in
/-- Each degreewise endomorphism `cornerComplexEndo i` is idempotent. -/
theorem cornerComplexEndo_idem (i : ι) :
    cornerComplexEndo.{v} J hc c i ≫ cornerComplexEndo.{v} J hc c i =
      cornerComplexEndo.{v} J hc c i := by
  ext K : 2
  exact HomologicalComplex.hom_ext _ _ fun n =>
    NatTrans.congr_app (sheafCentralEndo_idem J (he.idem i) (hc i)) (K.X n)

omit [DecidableEq ι] in
include he in
/-- The degreewise endomorphisms `cornerComplexEndo i` and `cornerComplexEndo j` are orthogonal
for `i ≠ j`. -/
theorem cornerComplexEndo_ortho (i j : ι) (hij : i ≠ j) :
    cornerComplexEndo.{v} J hc c i ≫ cornerComplexEndo.{v} J hc c j = 0 := by
  ext K n U m
  show e j • e i • m = 0
  rw [smul_smul, he.ortho hij.symm, zero_smul]

omit [DecidableEq ι] in
include he in
/-- The degreewise endomorphisms `cornerComplexEndo i` sum to the identity. -/
theorem cornerComplexEndo_sum :
    ∑ i, cornerComplexEndo.{v} J hc c i = 𝟙 _ := by
  ext K n U m
  let φ : (𝟭 (HomologicalComplex (Sheaf J (ModuleCat.{v} Λ)) c) ⟶ 𝟭 _) →+
      ((K.X n).obj.obj U) :=
    { toFun := fun t => (((t.app K).f n).hom.app U).hom m
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  show φ (∑ i, cornerComplexEndo.{v} J hc c i) = m
  rw [map_sum]
  show ∑ i, e i • m = m
  rw [← Finset.sum_smul, he.complete, one_smul]

/-- **A complete family of orthogonal central idempotents splits every complex.** For central
idempotents `e_i` of `Λ` with `e_i e_j = 0` for `i ≠ j` and `∑ e_i = 1`, every complex `C` of
sheaves of `Λ`-modules is the direct sum of its summands `e_i C`. -/
def cornerDecompositionIso (C : HomologicalComplex (Sheaf J (ModuleCat.{v} Λ)) c) :
    C ≅ ⨁ fun i => (cornerComplexPart.{v} J he hc c i).obj C :=
  idempotentDecompositionIso (cornerComplexEndo_idem.{v} J he hc c)
      (cornerComplexEndo_ortho.{v} J he hc c) (cornerComplexEndo_sum.{v} J he hc c) C ≪≫
    biproduct.mapIso fun i => ((cornerComplexPartIso.{v} J he hc c i).app C).symm

omit [DecidableEq ι] in
/-- The splitting `Stacks.EtaleCohomology.cornerDecompositionIso` is natural in the complex. -/
theorem cornerDecompositionIso_hom_naturality
    {C C' : HomologicalComplex (Sheaf J (ModuleCat.{v} Λ)) c} (f : C ⟶ C') :
    f ≫ (cornerDecompositionIso.{v} J he hc c C').hom =
      (cornerDecompositionIso.{v} J he hc c C).hom ≫
        biproduct.map fun i => (cornerComplexPart.{v} J he hc c i).map f := by
  classical
  rw [cornerDecompositionIso, cornerDecompositionIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc, idempotentDecompositionIso_hom_naturality, Category.assoc, Category.assoc]
  congr 1
  refine biproduct.hom_ext' _ _ (fun i => ?_)
  simp only [biproduct.mapIso_hom, biproduct.ι_map_assoc, biproduct.ι_map, Iso.symm_hom,
    Iso.app_inv]
  exact (cornerComplexPartIso.{v} J he hc c i).inv.naturality_assoc f _

end Decomposition

/-- **The primary corners of a finite ring.** A finite ring `Λ` has a complete family of
orthogonal central idempotents `e_i`, indexed by the primes `ℓ_i` dividing its characteristic,
whose corners `e_i Λ` are finite rings in which `ℓ_i ^ a_i = 0`. With
`Stacks.EtaleCohomology.cornerDecompositionIso` and `Stacks.EtaleCohomology.IsCtf.corner` this
splits `D_ctf(X, Λ)` into the pieces `D_ctf(X, e_i Λ)`, as in Step 3 of [Stacks, Tag 03UG]. -/
theorem exists_primary_corners (Λ : Type r) [Ring Λ] [Finite Λ] :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → Λ) (he : CompleteOrthogonalIdempotents e)
      (_hc : ∀ i (a : Λ), a * e i = e i * a) (ℓ a : ι → ℕ),
      (∀ i, (ℓ i).Prime) ∧ ∀ i, ((ℓ i ^ a i : ℕ) : (he.idem i).Corner) = 0 := by
  obtain ⟨ι, hι, e, ℓ, a, he, hc, hℓ, ha⟩ := exists_primary_completeOrthogonalIdempotents Λ
  exact ⟨ι, hι, e, he, hc, ℓ, a, hℓ, fun i =>
    natCast_corner_eq_zero (he.idem i) (hc i) _ (ha i)⟩

end Stacks.EtaleCohomology
