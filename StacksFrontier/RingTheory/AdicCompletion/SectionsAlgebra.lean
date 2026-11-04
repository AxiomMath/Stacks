module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties
public import StacksFrontier.RingTheory.Localization.Idempotent

/-!
# The sections algebra of an algebraization, and its canonical local pieces

Let `R → S` be a ring map and let a finite family of elements cut `Spec R` into the pieces a
formal-glueing datum is indexed by. These declarations build the algebra of compatible sections
over such a family: the local pieces `canonicalLocalCommRing` and `canonicalLocalAlgebra` with
their algebra maps, the comparison `canonicalAlphaAlgEquiv` of a localized module with the
localization of a module, the replacement `replaceGenericAlpha` of a glueing datum's generic
component by a canonical one, and the glued ring `glueX`.

They are the shared input of two developments that both algebraize along an adic completion -- the
ring-theoretic one in `RingTheory/AdicCompletion/Algebraization.lean` and the geometric one in
`AlgebraicGeometry/Normalization/BaseChangeToCompletion.lean` -- each of which carried its own copy
of all of it.
-/

@[expose] public section

open CategoryTheory FormalGlueing TensorProduct

universe u v w

/-- A linear map out of a localization of `B` at `S` is multiplicative as soon as it agrees with an
algebra map on the image of `B` and the elements of `S` act invertibly on the target. -/
theorem map_mul_of_isLocalizedModule
    {R B L T : Type*} [CommRing R] [CommRing B] [CommRing L] [CommRing T]
    [Algebra R B] [Algebra R L] [Algebra R T] (S : Submonoid R)
    (l : B →ₐ[R] L) [IsLocalizedModule S l.toLinearMap]
    (g : L →ₗ[R] T) (h : B →ₐ[R] T) (hg : ∀ b, g (l b) = h b)
    (hu : ∀ s : S, IsUnit (algebraMap R (Module.End R T) s)) (x y : L) :
    g (x * y) = g x * g y := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj S l.toLinearMap x
  obtain ⟨⟨b, t⟩, ht⟩ := IsLocalizedModule.surj S l.toLinearMap y
  have hunit := hu (s * t)
  rw [Module.End.isUnit_iff] at hunit
  apply hunit.1
  show ((s : R) * t) • g (x * y) = ((s : R) * t) • (g x * g y)
  change (s : R) • x = l a at hs
  change (t : R) • y = l b at ht
  rw [← map_smul, ← smul_mul_smul_comm, hs, ht, ← map_mul, hg, map_mul, ← smul_mul_smul_comm,
    ← map_smul, ← map_smul, hs, ht, hg, hg]

/-- Two linear maps into a module on which the elements of `S` act invertibly agree once they
agree after composition with a map that becomes bijective on localizing at `S`. -/
theorem linearMap_eq_of_localizedMap_bijective
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (S : Submonoid R) (q : M →ₗ[R] N)
    (hq : Function.Bijective (LocalizedModule.map S q))
    (hu : ∀ s : S, IsUnit (algebraMap R (Module.End R P) s))
    (g h : N →ₗ[R] P) (heq : g.comp q = h.comp q) : g = h := by
  let lM := LocalizedModule.mkLinearMap S M
  let lN := LocalizedModule.mkLinearMap S N
  let E := LinearEquiv.ofBijective ((LocalizedModule.map S q).restrictScalars R) hq
  have : IsLocalizedModule S (lN.comp q) := by
    convert IsLocalizedModule.of_linearEquiv S lM E using 1
    ext m
    exact (LocalizedModule.map_mk S q m 1).symm
  let G := IsLocalizedModule.lift S lN g hu
  let H := IsLocalizedModule.lift S lN h hu
  have hGH : G = H := by
    apply IsLocalizedModule.ext S (lN.comp q) hu
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      IsLocalizedModule.lift_comp, IsLocalizedModule.lift_comp, heq]
  exact (IsLocalizedModule.lift_comp S lN g hu).symm.trans
    ((congrArg (·.comp lN) hGH).trans (IsLocalizedModule.lift_comp S lN h hu))

/-- The image in `S` of a power of `f i` acts invertibly on the base change along `R → S` of the
Čech module at the index `{i}`, that module being a localization away from `f i`. -/
theorem tensor_cech_map_units
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (i : Fin r)
    (M : Type*) [AddCommGroup M] [Module R M]
    (s : Submonoid.powers (algebraMap R S (f i))) :
    IsUnit (algebraMap S (Module.End S (S ⊗[R] Cech.cechMod f M {i})) s) := by
  have : IsLocalizedModule (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) M) := by
    simpa [Cech.cechSub] using
      (inferInstance : IsLocalizedModule (Cech.cechSub f {i})
        (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) M))
  have := FormalGlueing.isLocalized_lTensor S (Submonoid.powers (f i))
    (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) M)
  obtain ⟨s, n, rfl⟩ := s
  have h := IsLocalizedModule.map_units
    ((LocalizedModule.mkLinearMap (Cech.cechSub f {i}) M).lTensor S)
    (⟨(f i) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (f i))
  rw [Module.End.isUnit_iff] at h ⊢
  show Function.Bijective (fun x : S ⊗[R] Cech.cechMod f M {i} =>
    (algebraMap R S (f i)) ^ n • x)
  change Function.Bijective (fun x : S ⊗[R] Cech.cechMod f M {i} => (f i) ^ n • x) at h
  simpa only [← map_pow, IsScalarTower.algebraMap_smul] using h

/-- The `i`-th comparison isomorphism of a glueing datum, transported along a map `q` out of its
generic piece which becomes bijective after localizing away from the image of `f i`. -/
noncomputable def replaceGenericAlpha
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (N : ModuleCat.{max u v w} S) (q : X.generic →ₗ[S] N)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q))
    (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) N ≃ₗ[S]
      S ⊗[R] restrictFromAway f i (X.localPiece i) :=
  (LinearEquiv.ofBijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q).restrictScalars S)
    (hq i)).symm.trans (X.alpha i)

/-- On fractions coming from the generic piece the transported comparison isomorphism agrees with
the original one. -/
theorem replaceGenericAlpha_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (N : ModuleCat.{max u v w} S) (q : X.generic →ₗ[S] N)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q))
    (i : Fin r) (m : X.generic) :
    replaceGenericAlpha f X N q hq i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) N (q m)) =
      X.alpha i (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ m) := by
  apply (X.alpha i).symm.injective
  simp only [replaceGenericAlpha, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  apply (LinearEquiv.ofBijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q).restrictScalars S)
    (hq i)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (LocalizedModule.map_mk _ q m 1).symm

/-- The glueing datum obtained from `X` by replacing its generic piece with an isomorphic module
`N`, keeping the local pieces and the overlap comparisons unchanged. -/
noncomputable def replaceGeneric
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (N : ModuleCat.{max u v w} S) (q : X.generic →ₗ[S] N)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q)) :
    ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) where
  generic := N
  localPiece := X.localPiece
  alpha := replaceGenericAlpha f X N q hq
  alphaIJ := X.alphaIJ
  cocycle := X.cocycle
  alpha_compatibility i j m := by
    let a i := (replaceGenericAlpha f X N q hq i).toLinearMap.comp
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) N)
    let g := (AlgebraTensorModule.lTensor S S (X.alphaIJ i j).toLinearMap).comp
      ((AlgebraTensorModule.lTensor S S
        (LocalizedModule.mkLinearMap (Cech.cechSub f {j}) _)).comp (a i))
    let h := (AlgebraTensorModule.lTensor S S
      (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) _)).comp (a j)
    have hgh : g = h := by
      apply linearMap_eq_of_localizedMap_bijective
        (Submonoid.powers (algebraMap R S (f i))) q (hq i)
        (tensor_cech_map_units f i _) g h
      ext x
      change TensorProduct.map LinearMap.id (X.alphaIJ i j).toLinearMap
          (TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (Cech.cechSub f {j}) _)
            (replaceGenericAlpha f X N q hq i (LocalizedModule.mkLinearMap _ _ (q x)))) =
        TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) _)
          (replaceGenericAlpha f X N q hq j (LocalizedModule.mkLinearMap _ _ (q x)))
      rw [replaceGenericAlpha_mk, replaceGenericAlpha_mk]
      exact X.alpha_compatibility i j x
    exact LinearMap.congr_fun hgh m

/-- If the induced map of localizations away from `a` is bijective, then the structure map `R → S`
becomes bijective after localizing at the powers of `a`. -/
theorem localizedModuleMap_bijective_of_awayMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (a : R)
    (h : Function.Bijective (IsLocalization.Away.map (Localization.Away a)
      (Localization.Away (algebraMap R S a)) (algebraMap R S) a)) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) (Algebra.linearMap R S)) := by
  let l := (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S a))).toLinearMap
  have : IsLocalizedModule (Submonoid.powers a) l := by
    apply isLocalizedModule_iff_isLocalization.mpr
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap R S a)
        (Localization.Away (algebraMap R S a)))
  let g : Localization.Away a →ₐ[R] Localization.Away (algebraMap R S a) :=
    { __ := IsLocalization.Away.map (Localization.Away a)
        (Localization.Away (algebraMap R S a)) (algebraMap R S) a
      commutes' r := by
        show IsLocalization.Away.map (Localization.Away a)
          (Localization.Away (algebraMap R S a)) (algebraMap R S) a
          (algebraMap R (Localization.Away a) r) = _
        rw [IsLocalization.Away.map, IsLocalization.map_eq]
        exact (IsScalarTower.algebraMap_apply R S _ r).symm }
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap R (Localization.Away a)) l).mp
  have hg : IsLocalizedModule.map (Submonoid.powers a)
      (Algebra.linearMap R (Localization.Away a)) l (Algebra.linearMap R S) =
      g.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers a)
      (Algebra.linearMap R (Localization.Away a)) (IsLocalizedModule.map_units l)
    rw [IsLocalizedModule.map_comp]
    exact LinearMap.ext fun r => (g.commutes r).symm
  rwa [hg]

/-- The canonical algebra map from `B` into its localization at `S`, sending `b` to `b / 1`. -/
noncomputable abbrev numeratorAlgHom
    {R : Type*} [CommRing R] (S : Submonoid R) (B : Type*) [CommRing B] [Algebra R B] :
    B →ₐ[R] LocalizedModule S B :=
  { __ := LocalizedModule.numeratorRingHom
    commutes' _ := rfl }

/-- A linear equivalence between two localizations of `B` at `S` that is compatible with the two
algebra maps out of `B` is an algebra equivalence. -/
noncomputable def algEquivOfIsLocalizedModule
    {R B L T : Type*} [CommRing R] [CommRing B] [CommRing L] [CommRing T]
    [Algebra R B] [Algebra R L] [Algebra R T] (S : Submonoid R)
    (l : B →ₐ[R] L) (h : B →ₐ[R] T)
    [IsLocalizedModule S l.toLinearMap] [IsLocalizedModule S h.toLinearMap]
    (E : L ≃ₗ[R] T) (hE : ∀ b, E (l b) = h b) : L ≃ₐ[R] T := by
  have h1 : E 1 = 1 := by simpa only [map_one] using hE 1
  exact AlgEquiv.ofLinearEquiv E h1 (map_mul_of_isLocalizedModule S l E.toLinearMap h hE
    (IsLocalizedModule.map_units h.toLinearMap))

/-- Restricting scalars along `R → A` does not change the underlying ring of an `A`-algebra. -/
noncomputable abbrev restrictScalarsCommRing
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing M] [Algebra A M] :
    CommRing ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) :=
  inferInstanceAs (CommRing M)

attribute [local instance] restrictScalarsCommRing

/-- The `i`-th local piece of the canonical glueing datum of an `R`-algebra `B` carries the ring
structure of the localization of `B` away from `f i`. -/
noncomputable abbrev canonicalLocalCommRing
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (B : Type w) [CommRing B] [Algebra R B] (i : Fin r) :
    CommRing (restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i)) :=
  inferInstanceAs (CommRing (LocalizedModule.Away (f i) B))

attribute [local instance] canonicalLocalCommRing

/-- An `A`-algebra is an `R`-algebra for the scalars restricted along `R → A`, its multiplication
being compatible with the induced `R`-action. -/
noncomputable abbrev restrictScalarsAlgebra
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing M] [Algebra A M] :
    Algebra R ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) := by
  letI : Module R ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) :=
    ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)).isModule
  letI : IsScalarTower A ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M))
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) :=
    inferInstanceAs (IsScalarTower A M M)
  letI : SMulCommClass A ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M))
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) :=
    inferInstanceAs (SMulCommClass A M M)
  exact Algebra.ofModule (fun r x y => smul_mul_assoc (algebraMap R A r) (x : M) (y : M))
    (fun r x y => mul_smul_comm (algebraMap R A r) (x : M) (y : M))

attribute [local instance] restrictScalarsCommRing restrictScalarsAlgebra

attribute [local instance] LocalizedModule.algebraOfIsLocalization

/-- The `i`-th local piece of the canonical glueing datum of an `R`-algebra `B` is again an
`R`-algebra. -/
noncomputable abbrev canonicalLocalAlgebra
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (B : Type w) [CommRing B] [Algebra R B] (i : Fin r) :
    Algebra R (restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i)) := by
  letI : Module R (restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i)) :=
    (restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i)).isModule
  apply Algebra.ofModule
  · intro r x y
    let E := canonicalLocalRestriction f (ModuleCat.of R B) i
    apply E.injective
    change E (r • x) * E y = E (r • (x * y))
    rw [map_smul, map_smul]
    exact smul_mul_assoc r (E x) (E y)
  · intro r x y
    let E := canonicalLocalRestriction f (ModuleCat.of R B) i
    apply E.injective
    change E x * E (r • y) = E (r • (x * y))
    rw [map_smul, map_smul]
    exact mul_smul_comm r (E x) (E y)

attribute [local instance] canonicalLocalAlgebra

/-- The algebra map from `B` into the `i`-th local piece of its canonical glueing datum, that is,
into its localization away from `f i`. -/
noncomputable def canonicalLocalAlgHom
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (B : Type w) [CommRing B] [Algebra R B] (i : Fin r) :
    B →ₐ[R] restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i) :=
  AlgHom.ofLinearMap (canonicalLocalMk f (ModuleCat.of R B) i)
    (map_one (LocalizedModule.numeratorRingHom (S := Submonoid.powers (f i))))
    (map_mul (LocalizedModule.numeratorRingHom (S := Submonoid.powers (f i))))

/-- The `i`-th comparison isomorphism of the canonical glueing datum of `S ⊗[R] B`, refined to an
`S`-algebra equivalence. -/
noncomputable def canonicalAlphaAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (B : Type w) [CommRing B] [Algebra R B] (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) (S ⊗[R] B) ≃ₐ[S]
      S ⊗[R] restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i) := by
  let l := numeratorAlgHom (Submonoid.powers (algebraMap R S (f i))) (S ⊗[R] B)
  let h := Algebra.TensorProduct.map (AlgHom.id S S) (canonicalLocalAlgHom f B i)
  have : IsLocalizedModule (Submonoid.powers (algebraMap R S (f i))) l.toLinearMap :=
    inferInstanceAs (IsLocalizedModule (Submonoid.powers (algebraMap R S (f i)))
      (LocalizedModule.mkLinearMap _ (S ⊗[R] B)))
  have : IsLocalizedModule (Submonoid.powers (algebraMap R S (f i))) h.toLinearMap :=
    canonicalTensor_isLocalized S f (ModuleCat.of R B) i
  apply algEquivOfIsLocalizedModule (Submonoid.powers (algebraMap R S (f i))) l h
    (canonicalAlpha S f (ModuleCat.of R B) i)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    change canonicalAlpha S f (ModuleCat.of R B) i
      (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] b)) =
        s ⊗ₜ[R] canonicalLocalMk f (ModuleCat.of R B) i b
    exact canonicalAlpha_mk S f (ModuleCat.of R B) i s b
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The overlap comparison of the canonical glueing datum of `B` over the intersection of the
`i`-th and `j`-th basic opens, refined to an `R`-algebra equivalence. -/
noncomputable def canonicalAlphaIJAlgEquiv
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (B : Type w) [CommRing B] [Algebra R B] (i j : Fin r) :
    Cech.cechMod f (restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i)) {j} ≃ₐ[R]
      Cech.cechMod f (restrictFromAway f j (canonicalLocalPiece f (ModuleCat.of R B) j)) {i} := by
  let l := (numeratorAlgHom (Cech.cechSub f {j}) _).comp (canonicalLocalAlgHom f B i)
  let h := (numeratorAlgHom (Cech.cechSub f {i}) _).comp (canonicalLocalAlgHom f B j)
  let U := Submonoid.closure (f '' (↑(({i} : Finset (Fin r)) ∪ {j}) : Set (Fin r)))
  have : IsLocalizedModule U l.toLinearMap :=
    canonicalOverlap_isLocalized f (ModuleCat.of R B) i {j}
  have : IsLocalizedModule U h.toLinearMap := by
    rw [show U = Submonoid.closure (f '' (↑(({j} : Finset (Fin r)) ∪ {i}) : Set (Fin r)))
      from by simp only [U, Finset.union_comm]]
    exact canonicalOverlap_isLocalized f (ModuleCat.of R B) j {i}
  exact algEquivOfIsLocalizedModule U l h (canonicalAlphaIJ f (ModuleCat.of R B) i j)
    (canonicalAlphaIJ_mk f (ModuleCat.of R B) i j)

/-- The algebra map induced on localizations at `S` by an algebra map `A → B`. -/
noncomputable def localizedAlgHomMap
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : Submonoid R) (q : A →ₐ[R] B) :
    LocalizedModule S A →ₐ[R] LocalizedModule S B := by
  let l := numeratorAlgHom S A
  let h := (numeratorAlgHom S B).comp q
  have : IsLocalizedModule S l.toLinearMap :=
    inferInstanceAs (IsLocalizedModule S (LocalizedModule.mkLinearMap S A))
  apply AlgHom.ofLinearMap ((LocalizedModule.map S q.toLinearMap).restrictScalars R)
  · calc
      (LocalizedModule.map S q.toLinearMap).restrictScalars R 1 =
          (LocalizedModule.map S q.toLinearMap).restrictScalars R (numeratorAlgHom S A 1) :=
        congrArg _ (map_one (numeratorAlgHom S A)).symm
      _ = numeratorAlgHom S B (q 1) := LocalizedModule.map_mk S q.toLinearMap 1 1
      _ = 1 := by rw [map_one, map_one]
  · exact map_mul_of_isLocalizedModule S l _ h (fun a => LocalizedModule.map_mk S q.toLinearMap a 1)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S B))

/-- The `i`-th comparison isomorphism of the canonical glueing datum of `S ⊗[R] B`, transported
along an algebra map to `T` that localizes to a bijection, as an `S`-algebra equivalence. -/
noncomputable def replaceGenericAlphaAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (B T : Type (max u v w)) [CommRing B] [CommRing T] [Algebra R B] [Algebra S T]
    (q : S ⊗[R] B →ₐ[S] T)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q.toLinearMap))
    (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) T ≃ₐ[S]
      S ⊗[R] restrictFromAway f i (canonicalLocalPiece f (ModuleCat.of R B) i) :=
  (AlgEquiv.ofBijective (localizedAlgHomMap (Submonoid.powers (algebraMap R S (f i))) q)
    (hq i)).symm.trans (canonicalAlphaAlgEquiv f B i)

/-- Localization at `S` preserves composition, so a composite of two maps that localize to
bijections localizes to a bijection. -/
theorem localizedModuleMap_bijective_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (S : Submonoid R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Bijective (LocalizedModule.map S f))
    (hg : Function.Bijective (LocalizedModule.map S g)) :
    Function.Bijective (LocalizedModule.map S (g.comp f)) := by
  have h : (LocalizedModule.map S (g.comp f)) =
      (LocalizedModule.map S g).comp (LocalizedModule.map S f) := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp [LocalizedModule.map_mk]
  rw [h]
  exact hg.comp hf

/-- The compatible sections of a glueing datum recover the generic piece after base change:
an `S`-linear equivalence carrying `s ⊗ x` to `s • x`. -/
theorem exists_sectionsGenericEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    ∃ E : S ⊗[R] compatibleSections S f (localizationComparisons f) X ≃ₗ[S] X.generic,
      ∀ (s : S) (x : compatibleSections S f (localizationComparisons f) X),
        E (s ⊗ₜ[R] x) = s • (show X.generic from x.1.1) := by
  let c := moduleGlueingConstruction.{u, v, w} S f
  let := c.category
  obtain ⟨e, hf, hi⟩ := FormalGlueing.canonicalFunctor_sections_areQuasiInverse R S f hflat hq
  let Y : c.canonical.obj (c.sections.obj X) ≅ X := by
    rw [← hf, ← hi]
    exact e.counitIso.app X
  have : IsIso c.canonicalSectionsUnit :=
    FormalGlueing.canonicalSectionsUnit_isIso R S f hflat hq
  let a : c.sections.obj X ≅ c.sections.obj X :=
    asIso (c.canonicalSectionsUnit.app (c.sections.obj X)) ≪≫ c.sections.mapIso Y
  let γ := ((FormalGlueing.genericProjection S f c).mapIso Y).toLinearEquiv
  let E := (AlgebraTensorModule.congr (LinearEquiv.refl S S) a.toLinearEquiv.symm).trans
    ((c.canonicalGeneric (c.sections.obj X)).symm.trans γ)
  refine ⟨E, fun s x => ?_⟩
  have hx := congrArg (fun y : compatibleSections S f (localizationComparisons f) X => y.1.1)
    (a.toLinearEquiv.apply_symm_apply x)
  change γ (1 ⊗ₜ[R] a.toLinearEquiv.symm x) = (show X.generic from x.1.1) at hx
  show γ (s ⊗ₜ[R] a.toLinearEquiv.symm x) = _
  have htmul : s ⊗ₜ[R] a.toLinearEquiv.symm x =
      s • (1 ⊗ₜ[R] a.toLinearEquiv.symm x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hγ : γ (s • (1 ⊗ₜ[R] a.toLinearEquiv.symm x)) =
      s • γ (1 ⊗ₜ[R] a.toLinearEquiv.symm x) := γ.map_smul s _
  exact (congrArg γ htmul).trans
    (hγ.trans (congrArg (fun z : X.generic => s • z) hx))

/-- The transported comparison isomorphism of the canonical glueing datum agrees, as a map, with
its refinement to an algebra equivalence. -/
theorem replaceGenericAlpha_canonical_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (B T : Type (max u v w)) [CommRing B] [CommRing T]
    [Algebra R B] [Algebra S T] (q : S ⊗[R] B →ₐ[S] T)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q.toLinearMap))
    (i : Fin r) (z : LocalizedModule.Away (algebraMap R S (f i)) T) :
    replaceGenericAlpha.{u, v, w} f (canonicalDatum S f (ModuleCat.of R B)) (ModuleCat.of S T)
        q.toLinearMap hq i z =
      replaceGenericAlphaAlgEquiv.{u, v, w} f B T q hq i z := by
  obtain ⟨y, rfl⟩ := (hq i).2 z
  simp only [replaceGenericAlpha, replaceGenericAlphaAlgEquiv, LinearEquiv.trans_apply,
    AlgEquiv.trans_apply]
  have h1 := (LinearEquiv.ofBijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
      q.toLinearMap).restrictScalars S) (hq i)).symm_apply_apply y
  have h2 := (AlgEquiv.ofBijective (localizedAlgHomMap (Submonoid.powers (algebraMap R S (f i))) q)
    (hq i)).symm_apply_apply y
  exact (congrArg (fun t ↦ (canonicalDatum S f (ModuleCat.of R B)).alpha i t) h1).trans
    (congrArg (fun t ↦ canonicalAlphaAlgEquiv (S := S) f B i t) h2).symm

/-! ### The algebra of compatible sections of a glued datum

The declarations below build, from an `R`-algebra `B`, an `S`-algebra `T` and an algebra map
`q : S ⊗[R] B →ₐ[S] T` which is an isomorphism after localizing away from each `f i`, the
`R`-subalgebra `sectionsSubalgebra` of compatible sections of the glueing datum `glueX`, and
record its two properties every consumer needs: its base change to `S` is `T`, and it is finite
over `R` when `T` is finite over `S` and `B` is finite over `R`.

They live here rather than in any one consumer because the three developments that algebraize
along an adic completion -- `RingTheory/AdicCompletion/Algebraization.lean`,
`RingTheory/Localization/Glueing/RingHomGluing/MaximalIdealGluing.lean` and
`AlgebraicGeometry/Normalization/BaseChangeToCompletion.lean` -- each need all of it and none of
them imports the others.
-/

namespace FormalGlueing

/-- The compatible sections of a glueing datum form a finite `R`-module as soon as the generic
piece is finite over `S` and each local piece is finite over the corresponding localization. -/
theorem finite_compatibleSections
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    [Module.Finite S X.generic]
    [∀ i, Module.Finite (Localization.Away (f i)) (X.localPiece i)] :
    Module.Finite R (compatibleSections S f (localizationComparisons f) X) := by
  let c := moduleGlueingConstruction.{u, v, w} S f
  let := c.category
  obtain ⟨st, gt, lt, ct, e, h⟩ :=
    FormalGlueing.formalGlueing_preserves_moduleProperties_tensor_and_algebras.1
      R S r f hflat hq
  obtain ⟨_, _, _, _, _, _, _, _, hf, hi, hfinite, _⟩ := h
  have H : Module.Finite R (e.inverse.obj X) := by
    apply (hfinite _).1.mpr
    constructor
    · let E : X.generic ≃ₗ[S] (e.functor.obj (e.inverse.obj X)).generic :=
        (((FormalGlueing.genericProjection S f c).mapIso (e.counitIso.app X)).symm.toLinearEquiv)
      exact Module.Finite.equiv E
    · intro i
      let E : X.localPiece i ≃ₗ[Localization.Away (f i)]
          (e.functor.obj (e.inverse.obj X)).localPiece i :=
        (((FormalGlueing.localProjection S f c i).mapIso (e.counitIso.app X)).symm.toLinearEquiv)
      exact Module.Finite.equiv E
  show Module.Finite R (c.sections.obj X)
  rwa [hi] at H

/-- The `i`-th local piece of the canonical glueing datum of an `R`-algebra `C`, read as an
`R`-module: the localization of `C` away from `g i`, with its scalars restricted to `R`. -/
noncomputable abbrev awayLocalPiece {A : Type u} [CommRing A] {n : ℕ} (g : Fin n → A)
    (C : Type w) [CommRing C] [Algebra A C] (i : Fin n) : ModuleCat.{max u w} A :=
  restrictFromAway g i (canonicalLocalPiece g (ModuleCat.of A C) i)

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (B T : Type (max u v w)) [CommRing B] [CommRing T]
    [Algebra R B] [Algebra S T] (q : S ⊗[R] B →ₐ[S] T)
    (hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) q.toLinearMap))

/-- The canonical glueing datum of the `R`-algebra `B` with its generic piece replaced by `T` along
the algebra map `q`. -/
noncomputable def glueX : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) :=
  replaceGeneric.{u, v, w} f (canonicalDatum S f (ModuleCat.of R B)) (ModuleCat.of S T)
    q.toLinearMap hq

/-- Membership in the module of compatible sections of `glueX`, written out as compatibility of the
generic component with each local piece and of the local pieces with each other. -/
theorem mem_sections_iff (x : T × ∀ i, awayLocalPiece f B i) :
    x ∈ compatibleSections S f (localizationComparisons f) (glueX f B T q hq) ↔
      (∀ i, replaceGenericAlphaAlgEquiv f B T q hq i
          (numeratorAlgHom (Submonoid.powers (algebraMap R S (f i))) T x.1) =
            (1 : S) ⊗ₜ[R] x.2 i) ∧
      ∀ i j, canonicalAlphaIJAlgEquiv f B i j
          (numeratorAlgHom (Cech.cechSub f {j}) _ (x.2 i)) =
            numeratorAlgHom (Cech.cechSub f {i}) _ (x.2 j) := by
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  exact Eq.congr_left (replaceGenericAlpha_canonical_eq f B T q hq i _)

variable [Algebra R T] [IsScalarTower R S T]

/-- The compatible sections of `glueX` form an `R`-subalgebra of the product of `T` with the local
pieces: they are closed under products and contain the image of `R`. -/
noncomputable def sectionsSubalgebra : Subalgebra R (T × ∀ i, awayLocalPiece f B i) where
  carrier := {x | x ∈ compatibleSections S f (localizationComparisons f) (glueX f B T q hq)}
  add_mem' :=
    Submodule.add_mem (compatibleSections S f (localizationComparisons f) (glueX f B T q hq))
  zero_mem' :=
    Submodule.zero_mem (compatibleSections S f (localizationComparisons f) (glueX f B T q hq))
  mul_mem' := by
    intro x y hx hy
    have hx := (mem_sections_iff f B T q hq x).1 hx
    have hy := (mem_sections_iff f B T q hq y).1 hy
    apply (mem_sections_iff f B T q hq (x * y)).2
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · rw [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, map_mul, hx.1 i, hy.1 i,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    · rw [Prod.snd_mul, Pi.mul_apply, Pi.mul_apply, map_mul, map_mul, map_mul, hx.2 i j,
        hy.2 i j]
  one_mem' := by
    apply (mem_sections_iff f B T q hq 1).2
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · rw [Prod.fst_one, Prod.snd_one, Pi.one_apply, map_one, map_one]
      rfl
    · rw [Prod.snd_one, Pi.one_apply, Pi.one_apply, map_one, map_one, map_one]
  algebraMap_mem' a := by
    apply (mem_sections_iff f B T q hq _).2
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · change replaceGenericAlphaAlgEquiv f B T q hq i
        (numeratorAlgHom _ T (algebraMap R T a)) =
          (1 : S) ⊗ₜ[R] algebraMap R (awayLocalPiece f B i) a
      rw [IsScalarTower.algebraMap_apply R S T, AlgHom.commutes, AlgEquiv.commutes,
        Algebra.algebraMap_eq_smul_one (A := awayLocalPiece f B i),
        TensorProduct.tmul_smul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul']
    · change canonicalAlphaIJAlgEquiv f B i j
        (numeratorAlgHom _ _ (algebraMap R (awayLocalPiece f B i) a)) =
          numeratorAlgHom _ _ (algebraMap R (awayLocalPiece f B j) a)
      rw [AlgHom.commutes, AlgEquiv.commutes, AlgHom.commutes]

/-- The algebra of compatible sections and the module of compatible sections of `glueX` have the
same underlying `R`-module. -/
noncomputable def sectionsSubalgebraLinearEquiv :
    sectionsSubalgebra f B T q hq ≃ₗ[R]
      compatibleSections S f (localizationComparisons f) (glueX f B T q hq) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    ext
    · change a • (x : T × ∀ i, awayLocalPiece f B i).1 =
        algebraMap R S a • (x : T × ∀ i, awayLocalPiece f B i).1
      rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S T]
    · rfl

/-- Base change to `S` of the algebra of compatible sections recovers `T`, as `S`-algebras, by an
equivalence carrying `s ⊗ x` to `s` times the generic component of `x`. -/
theorem exists_algEquiv_tensor_sectionsSubalgebra (hflat : Module.Flat R S)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    ∃ E : S ⊗[R] sectionsSubalgebra f B T q hq ≃ₐ[S] T,
      ∀ (s : S) (x : sectionsSubalgebra f B T q hq),
        E (s ⊗ₜ[R] x) = s • (x : T × ∀ i, awayLocalPiece f B i).1 := by
  obtain ⟨E, hE⟩ := exists_sectionsGenericEquiv f hflat hquot (glueX f B T q hq)
  let E' : S ⊗[R] sectionsSubalgebra f B T q hq ≃ₗ[S] T :=
    (AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (sectionsSubalgebraLinearEquiv f B T q hq)).trans E
  have hE' (s : S) (x : sectionsSubalgebra f B T q hq) :
      E' (s ⊗ₜ[R] x) = s • (x : T × ∀ i, awayLocalPiece f B i).1 := hE s _
  refine ⟨Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct E' ?_ ?_, ?_⟩
  · intro s₁ s₂ x₁ x₂
    rw [hE', hE', hE', Subalgebra.coe_mul, Prod.fst_mul, Algebra.smul_def, Algebra.smul_def,
      Algebra.smul_def, map_mul]
    ring
  · rw [hE', one_smul]
    rfl
  · intro s x
    exact hE' s x

/-- The algebra of compatible sections is finite over `R` when `T` is finite over `S` and `B` is
finite over `R`. -/
theorem finite_sectionsSubalgebra (hflat : Module.Flat R S)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    [Module.Finite S T] [Module.Finite R B] :
    Module.Finite R (sectionsSubalgebra f B T q hq) := by
  have : Module.Finite S (glueX f B T q hq).generic := inferInstanceAs (Module.Finite S T)
  have : ∀ i, Module.Finite (Localization.Away (f i)) ((glueX f B T q hq).localPiece i) := by
    intro i
    show Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) B)
    exact Module.Finite.of_isLocalizedModule (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
  have := finite_compatibleSections f hflat hquot (glueX f B T q hq)
  exact Module.Finite.equiv (sectionsSubalgebraLinearEquiv f B T q hq).symm

end

end FormalGlueing
