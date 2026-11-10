module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.AffineSections

/-!
# Realizing a square-zero extension of the structure sheaf by a scheme

The affine charts of the locally ringed space defined by a square-zero extension with
quasi-coherent kernel are affine schemes, so it is a scheme, in which `X` is a first-order
thickening over the base.

## Main definitions

* `Stacks.Thickenings.Realization`: the scheme realizing such an extension, with its
  first-order thickening over the base.

## Main results

* `Stacks.Thickenings.squareZeroExtension_realization`: a square-zero extension with
  quasi-coherent kernel is realized by a first-order thickening.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

private theorem specComap_isHomeomorph_of_surjective_squareZero
    {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T)
    (hf : Function.Surjective f)
    (hker : ∀ r ∈ RingHom.ker f, r ^ 2 = 0) :
    IsHomeomorph (PrimeSpectrum.comap f) := by
  apply PrimeSpectrum.isHomeomorph_comap f
  · intro t
    obtain ⟨r, rfl⟩ := hf t
    exact ⟨1, by omega, ⟨r, by simp⟩⟩
  · intro r hr
    rw [mem_nilradical]
    exact ⟨2, by simpa [pow_two] using hker r hr⟩

private abbrev commRingToAddCommGrp : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

private noncomputable def commRingStalkToAddCommGrpStalkIso
    {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X) (x : X) :
    (commRingToAddCommGrp.obj
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj F.presheaf)) ≅
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
        (F.presheaf ⋙ commRingToAddCommGrp) :=
  preservesColimitIso commRingToAddCommGrp ((OpenNhds.inclusion x).op ⋙ F.presheaf)

private theorem commRingStalkToAddCommGrpStalkIso_germ
    {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    commRingToAddCommGrp.map (TopCat.Presheaf.germ F.presheaf U x hx) ≫
        (commRingStalkToAddCommGrpStalkIso F x).hom =
      TopCat.Presheaf.germ (F.presheaf ⋙ commRingToAddCommGrp) U x hx :=
  ι_preservesColimitIso_hom commRingToAddCommGrp
    ((OpenNhds.inclusion x).op ⋙ F.presheaf) (Opposite.op ⟨U, hx⟩)

private theorem isIso_stalkMap_of_isOpenImmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (z : X) : IsIso (g.stalkMap z) := inferInstance

private theorem squareZero_affineChartInclusion_base
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) :
    (squareZero_affineChartInclusion E U).base = 𝟙 (TopCat.of U) := by
  dsimp only [squareZero_affineChartInclusion, LocallyRingedSpace.homMk]
  rfl

private theorem squareZero_affineChartInclusion_toΓSpec_naturality
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) :
    squareZero_affineChartInclusion E U ≫
        LocallyRingedSpace.toΓSpec (thickenedAffineChart E U) =
      LocallyRingedSpace.toΓSpec (X.restrict U.ι.isOpenEmbedding).toLocallyRingedSpace ≫
        Spec.toLocallyRingedSpace.map
          (LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op).op :=
  ΓSpec.locallyRingedSpaceAdjunction.unit.naturality
    (squareZero_affineChartInclusion E U)

private theorem squareZero_affineChartInclusion_Γ_comp
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) :
    let h := U.ι.isOpenEmbedding
    let htop : h.functor.obj ⊤ = U := U.ι_image_top
    let eA := E.A.presheaf.mapIso (eqToIso htop).op
    let eX := (X.sheaf.presheaf.mapIso (eqToIso htop).op).symm
    eA.hom ≫ LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op ≫ eX.hom =
      E.π.hom.app (Opposite.op U) := by
  dsimp
  let h := U.ι.isOpenEmbedding
  have htop : h.functor.obj ⊤ = U := U.ι_image_top
  have hnat := E.π.hom.naturality (eqToHom htop).op
  change E.A.obj.map (eqToHom htop).op ≫
      E.π.hom.app (Opposite.op (h.functor.obj ⊤)) ≫
      X.sheaf.obj.map ((eqToIso htop).op.inv) = E.π.hom.app (Opposite.op U)
  calc
    E.A.obj.map (eqToHom htop).op ≫
        E.π.hom.app (Opposite.op (h.functor.obj ⊤)) ≫
        X.sheaf.obj.map ((eqToIso htop).op.inv) =
      (E.π.hom.app (Opposite.op U) ≫ X.sheaf.obj.map (eqToHom htop).op) ≫
        X.sheaf.obj.map ((eqToIso htop).op.inv) :=
          congrArg (fun q => q ≫ X.sheaf.obj.map ((eqToIso htop).op.inv)) hnat
    _ = E.π.hom.app (Opposite.op U) := by
      have hd : (eqToHom htop).op ≫ (eqToIso htop).op.inv =
          𝟙 (Opposite.op U) :=
        (eqToIso htop).op.hom_inv_id
      calc
        _ = E.π.hom.app (Opposite.op U) ≫
            (X.sheaf.obj.map (eqToHom htop).op ≫
              X.sheaf.obj.map ((eqToIso htop).op.inv)) := by
              rw [Category.assoc]
        _ = E.π.hom.app (Opposite.op U) ≫
            X.sheaf.obj.map ((eqToHom htop).op ≫ (eqToIso htop).op.inv) := by
              rw [← Functor.map_comp]
        _ = E.π.hom.app (Opposite.op U) := by
              rw [hd]
              rw [X.sheaf.obj.map_id, Category.comp_id]

private theorem squareZero_affineChartInclusion_Γ_kernel
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens)
    (htop : U.ι.isOpenEmbedding.functor.obj ⊤ = U) :
    ∀ a, a ∈ RingHom.ker
        (LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op).hom ↔
      ∃ z, (E.A.presheaf.mapIso (eqToIso htop).op).hom.hom
        (E.ι (Opposite.op U) z) = a := by
  let h := U.ι.isOpenEmbedding
  let eA := E.A.presheaf.mapIso (eqToIso htop).op
  let eX := (X.sheaf.presheaf.mapIso (eqToIso htop).op).symm
  let g := (LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op).hom
  have hcomp := squareZero_affineChartInclusion_Γ_comp E U
  have heX : Function.Bijective eX.hom.hom :=
    (ConcreteCategory.isIso_iff_bijective eX.hom).mp inferInstance
  intro b
  constructor
  · intro hb
    let a := eA.inv.hom b
    have hba : eA.hom.hom a = b := by
      dsimp [a]
      have hh : eA.hom.hom.comp eA.inv.hom = RingHom.id _ := by
        simpa only [CommRingCat.hom_comp, CommRingCat.hom_id] using
          congrArg CommRingCat.Hom.hom eA.inv_hom_id
      exact congrArg (fun q => q b) hh
    have hπ : (E.π.hom.app (Opposite.op U)).hom a = 0 := by
      have h := congrArg (fun q => q a) hcomp
      change eX.hom.hom (g (eA.hom.hom a)) =
        (E.π.hom.app (Opposite.op U)).hom a at h
      rw [hba, RingHom.mem_ker.mp hb] at h
      have hzero : eX.hom.hom 0 = 0 := map_zero _
      calc
        _ = eX.hom.hom 0 := h.symm
        _ = 0 := hzero
    obtain ⟨z, hz⟩ := (squareZero_sectionMap_kernel_eq_range E
      (Opposite.op U) a).mp hπ
    refine ⟨z, ?_⟩
    rw [hz, hba]
  · rintro ⟨z, hz⟩
    have hπ := E.mem_kernel (Opposite.op U) z
    have h := congrArg (fun q => q (E.ι (Opposite.op U) z)) hcomp
    change eX.hom.hom (g (eA.hom.hom (E.ι (Opposite.op U) z))) =
      (E.π.hom.app (Opposite.op U)).hom (E.ι (Opposite.op U) z) at h
    rw [hπ, hz] at h
    exact RingHom.mem_ker.mpr (heX.1 (h.trans (map_zero _).symm))

private theorem squareZero_affineChartInclusion_Γ_surjective
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective
      (LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op).hom := by
  let h := U.ι.isOpenEmbedding
  let htop : h.functor.obj ⊤ = U := U.ι_image_top
  let eA := E.A.presheaf.mapIso (eqToIso htop).op
  let eX := (X.sheaf.presheaf.mapIso (eqToIso htop).op).symm
  let g := (LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op).hom
  have hcomp := squareZero_affineChartInclusion_Γ_comp E U
  intro b
  obtain ⟨a, ha⟩ := squareZero_sectionMap_surjective_of_affine E U hU (eX.hom.hom b)
  refine ⟨eA.hom.hom a, ?_⟩
  have hinj : Function.Injective eX.hom :=
    (ConcreteCategory.isIso_iff_bijective eX.hom).mp inferInstance |>.1
  exact hinj ((congrArg (fun q => q a) hcomp).trans ha)

private theorem squareZero_affineChartInclusion_Γ_ker
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) :
    ∀ a ∈ RingHom.ker
      (LocallyRingedSpace.Γ.map (squareZero_affineChartInclusion E U).op).hom,
      a ^ 2 = 0 := by
  let htop : U.ι.isOpenEmbedding.functor.obj ⊤ = U := U.ι_image_top
  intro b hb
  obtain ⟨z, hz⟩ := squareZero_affineChartInclusion_Γ_kernel E U htop b |>.mp hb
  calc
    b ^ 2 = ((E.A.presheaf.mapIso (eqToIso htop).op).hom.hom
        (E.ι (Opposite.op U) z)) ^ 2 := congrArg (fun w => w ^ 2) hz.symm
    _ = (E.A.presheaf.mapIso (eqToIso htop).op).hom.hom
        ((E.ι (Opposite.op U) z) ^ 2) := (map_pow _ _ 2).symm
    _ = 0 := by rw [pow_two, E.square_zero, map_zero]

private theorem squareZero_affineChartToSpec_base_isHomeomorph
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsHomeomorph (thickenedAffineChartToSpec E U).base := by
  let f₀ := squareZero_affineChartInclusion E U
  let t := thickenedAffineChartToSpec E U
  let s := LocallyRingedSpace.toΓSpec
    (X.restrict U.ι.isOpenEmbedding).toLocallyRingedSpace
  have hnat := squareZero_affineChartInclusion_toΓSpec_naturality E U
  have hfbase : f₀.base = 𝟙 (TopCat.of U) :=
    squareZero_affineChartInclusion_base E U
  have hspec : IsHomeomorph
      (Spec.toLocallyRingedSpace.map (LocallyRingedSpace.Γ.map f₀.op).op).base := by
    change IsHomeomorph (PrimeSpectrum.comap
      (LocallyRingedSpace.Γ.map f₀.op).hom)
    exact specComap_isHomeomorph_of_surjective_squareZero _
      (squareZero_affineChartInclusion_Γ_surjective E U hU)
      (squareZero_affineChartInclusion_Γ_ker E U)
  have hs : IsHomeomorph s.base := by
    have : IsAffine (X.restrict U.ι.isOpenEmbedding) := hU
    have hsIso : IsIso s := by
      change IsIso (Scheme.forgetToLocallyRingedSpace.map
        (X.restrict U.ι.isOpenEmbedding).toSpecΓ)
      infer_instance
    let : IsIso s := hsIso
    have hbase : IsIso (LocallyRingedSpace.forgetToTop.map s) := by
      infer_instance
    exact (TopCat.isIso_iff_isHomeomorph _).mp hbase
  have hcomp : f₀.base ≫ t.base = s.base ≫
      (Spec.toLocallyRingedSpace.map (LocallyRingedSpace.Γ.map f₀.op).op).base :=
    congrArg (fun q => q.toHom.base) hnat
  have hcomp' (x : U) : t.base x =
      (Spec.toLocallyRingedSpace.map (LocallyRingedSpace.Γ.map f₀.op).op).base (s.base x) := by
    have hx := congrArg (fun q => q x) hcomp
    change t.base (f₀.base x) =
      (Spec.toLocallyRingedSpace.map (LocallyRingedSpace.Γ.map f₀.op).op).base (s.base x) at hx
    rwa [hfbase] at hx
  change IsHomeomorph (fun x : U => t.base x)
  rw [funext hcomp']
  exact hspec.comp hs

private theorem squareZero_affineChartToSpec_isIso_of_stalkMap_isIso
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hstalk : ∀ x : U, IsIso ((thickenedAffineChartToSpec E U).stalkMap x)) :
    IsIso (thickenedAffineChartToSpec E U) :=
  locallyRingedSpace_hom_isIso_of_base_homeomorph (thickenedAffineChartToSpec E U)
    (squareZero_affineChartToSpec_base_isHomeomorph E U hU) hstalk

private theorem locallyRingedSpace_toΓSpec_stalk_germ
    (T : LocallyRingedSpace.{u}) (x : T)
    (r : LocallyRingedSpace.Γ.obj (Opposite.op T)) :
    ((T.toΓSpec).stalkMap x).hom
      (StructureSheaf.toStalk (LocallyRingedSpace.Γ.obj (Opposite.op T))
        ((T.toΓSpec).base x) r) = T.presheaf.Γgerm x r :=
  ConcreteCategory.congr_hom
    (LocallyRingedSpace.toStalk_stalkMap_toΓSpec T x) r

private theorem thickenedAffineChart_restrictStalkIso_germ
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (x : U)
    (r : (thickenedAffineChart E U).presheaf.obj (Opposite.op ⊤)) :
    ((thickenedAffineChart E U).presheaf.germ ⊤ x (by trivial) ≫
      ((thickenedLocallyRingedSpace E).restrictStalkIso U.ι.isOpenEmbedding x).hom) r =
    (thickenedLocallyRingedSpace E).presheaf.germ
      (U.ι.isOpenEmbedding.functor.obj ⊤) (U.ι x) (by
        change U.ι x ∈ U.ι ''ᵁ ⊤
        exact ⟨x, Set.mem_univ _, rfl⟩) r :=
  ConcreteCategory.congr_hom
    (LocallyRingedSpace.restrictStalkIso_hom_eq_germ
      (X := thickenedLocallyRingedSpace E) U.ι.isOpenEmbedding ⊤ x
      (by trivial)) r

private theorem isLocalization_of_exact_comparison
    {R B T C I J : Type*} [CommRing R] [CommRing B] [CommRing T] [CommRing C]
    [AddCommGroup I] [AddCommGroup J] [Module B I] [Module B J]
    (π : R →+* B) (f : R →+* T) (g : B →+* C) (p : T →+* C)
    (ι : I →+ R) (j : J →+ T) (k : I →ₗ[B] J)
    (S : Submonoid B) [Algebra B C] [IsLocalization S C]
    (hg : g = algebraMap B C)
    (hπ : Function.Surjective π)
    (hcomm : ∀ a, p (f a) = g (π a))
    (hι : ∀ a, π a = 0 → ∃ m, ι m = a)
    (hj : ∀ t, p t = 0 → ∃ z, j z = t)
    (hjinj : Function.Injective j)
    (hjk : ∀ m, j (k m) = f (ι m))
    (hιsmul : ∀ r m, ι (π r • m) = r * ι m)
    (hjsmul : ∀ r z, j (π r • z) = f r * j z)
    (hk : IsLocalizedModule S k)
    (hunit : ∀ s : S.comap π, IsUnit (f s)) :
    letI := f.toAlgebra
    IsLocalization (S.comap π) T := by
  subst hg
  let := hk
  let := f.toAlgebra
  have hzero (a : R) (ha : f a = 0) : ∃ r : S.comap π, r.val * a = 0 := by
    have hga : algebraMap B C (π a) = 0 := by rw [← hcomm, ha, map_zero]
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff S C (π a)).mp hga
    obtain ⟨r, hr⟩ := hπ s.val
    obtain ⟨m, hm⟩ := hι (r * a) (by rw [map_mul, hr]; exact hs)
    have hkm : k m = 0 := hjinj (by rw [hjk, hm, map_mul, ha, mul_zero, map_zero])
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff S k).mp hkm
    change s'.val • m = 0 at hs'
    obtain ⟨r', hr'⟩ := hπ s'.val
    refine ⟨⟨r' * r, ?_⟩, ?_⟩
    · change π (r' * r) ∈ S
      rw [map_mul, hr', hr]
      exact S.mul_mem s'.property s.property
    · calc
        r' * r * a = r' * ι m := by rw [hm]; ring
        _ = ι (π r' • m) := (hιsmul r' m).symm
        _ = 0 := by rw [hr', hs', map_zero]
  apply (isLocalization_iff (S.comap π) T).2
  refine ⟨hunit, ?_, ?_⟩
  · intro t
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj S (p t)
    obtain ⟨a, ha⟩ := hπ b
    obtain ⟨r, hr⟩ := hπ s.val
    have hp : p (f r * t - f a) = 0 := by
      rw [map_sub, map_mul, hcomm, hcomm, hr, ha, mul_comm, hs, sub_self]
    obtain ⟨z, hz⟩ := hj _ hp
    obtain ⟨⟨m, s'⟩, hm⟩ := IsLocalizedModule.surj (S := S) (f := k) z
    change s'.val • z = k m at hm
    obtain ⟨r', hr'⟩ := hπ s'.val
    refine ⟨⟨r' * a + ι m, ⟨r * r', ?_⟩⟩, ?_⟩
    · change π (r * r') ∈ S
      rw [map_mul, hr, hr']
      exact S.mul_mem s.property s'.property
    · have he : f r' * (f r * t - f a) = f (ι m) := by
        rw [← hz, ← hjsmul, hr', hm, hjk]
      change t * f (r * r') = f (r' * a + ι m)
      rw [map_add, map_mul, map_mul, ← he]
      ring
  · intro a b hab
    change f a = f b at hab
    obtain ⟨r, hr⟩ := hzero (a - b) (by rw [map_sub, hab, sub_self])
    refine ⟨r, ?_⟩
    exact sub_eq_zero.mp (by simpa only [mul_sub] using hr)

private noncomputable def squareZero_kernelStalkInclusion
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    E.I.presheaf.stalk x →+ TopCat.Presheaf.stalk (C := CommRingCat.{u}) E.A.presheaf x :=
  (commRingStalkToAddCommGrpStalkIso E.A x).inv.hom.comp
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (squareZero_kernelSheafInclusion E).hom).hom)

private theorem squareZero_kernelStalkInclusion_germ
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(E.I, U)) :
    squareZero_kernelStalkInclusion E x (E.I.presheaf.germ U x hx m) =
      TopCat.Presheaf.germ E.A.presheaf U x hx (E.ι (Opposite.op U) m) := by
  have he := ConcreteCategory.congr_hom
    (commRingStalkToAddCommGrpStalkIso_germ E.A x U hx) (E.ι (Opposite.op U) m)
  change (commRingStalkToAddCommGrpStalkIso E.A x).inv
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (squareZero_kernelSheafInclusion E).hom) (E.I.presheaf.germ U x hx m)) = _
  rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (squareZero_kernelSheafInclusion E).hom) (E.I.presheaf.germ U x hx m) =
      TopCat.Presheaf.germ (E.A.presheaf ⋙ commRingToAddCommGrp) U x hx
        (E.ι (Opposite.op U) m) from
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      (squareZero_kernelSheafInclusion E).hom m]
  exact (DFunLike.congr_arg
      (ConcreteCategory.hom (commRingStalkToAddCommGrpStalkIso E.A x).inv) he).symm.trans
    (ConcreteCategory.congr_hom (commRingStalkToAddCommGrpStalkIso E.A x).hom_inv_id _)

private theorem squareZero_kernelStalkInclusion_smul
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : E.A.presheaf.obj (Opposite.op U))
    (z : E.I.presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x) (E.I.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) E.I.val x
    squareZero_kernelStalkInclusion E x
        (X.presheaf.germ U x hx (E.π.hom.app (Opposite.op U) a) • z) =
      TopCat.Presheaf.germ E.A.presheaf U x hx a * squareZero_kernelStalkInclusion E x z := by
  let : Module (X.presheaf.stalk x) (E.I.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) E.I.val x
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.I.presheaf z
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hx, hxV⟩
  let l : W ⟶ U := homOfLE inf_le_left
  let r : W ⟶ V := homOfLE inf_le_right
  let a' := E.A.presheaf.map l.op a
  let m' := E.I.val.map r.op m
  have ha : TopCat.Presheaf.germ E.A.presheaf W x hxW a' =
      TopCat.Presheaf.germ E.A.presheaf U x hx a :=
    TopCat.Presheaf.germ_res_apply E.A.presheaf l x hxW a
  have hm : E.I.presheaf.germ W x hxW m' = E.I.presheaf.germ V x hxV m :=
    TopCat.Presheaf.germ_res_apply E.I.presheaf r x hxW m
  have hb : X.presheaf.germ W x hxW (E.π.hom.app (Opposite.op W) a') =
      X.presheaf.germ U x hx (E.π.hom.app (Opposite.op U) a) := by
    have he := ConcreteCategory.congr_hom (E.π.hom.naturality l.op) a
    change E.π.hom.app (Opposite.op W) a' =
      X.presheaf.map l.op (E.π.hom.app (Opposite.op U) a) at he
    rw [he]
    exact TopCat.Presheaf.germ_res_apply X.presheaf l x hxW _
  calc squareZero_kernelStalkInclusion E x
        (X.presheaf.germ U x hx (E.π.hom.app (Opposite.op U) a) •
          E.I.presheaf.germ V x hxV m)
      = squareZero_kernelStalkInclusion E x
          (X.presheaf.germ W x hxW (E.π.hom.app (Opposite.op W) a') •
            E.I.presheaf.germ W x hxW m') := by rw [hb, hm]
    _ = squareZero_kernelStalkInclusion E x
          (E.I.presheaf.germ W x hxW
            (((E.I.val.obj (Opposite.op W)).smul
              (E.π.hom.app (Opposite.op W) a')).asHom.hom m')) :=
        DFunLike.congr_arg (squareZero_kernelStalkInclusion E x)
          (PresheafOfModules.germ_smul (R := X.presheaf) E.I.val x W hxW
            (E.π.hom.app (Opposite.op W) a') m').symm
    _ = TopCat.Presheaf.germ E.A.presheaf W x hxW
          (E.ι (Opposite.op W)
            (((E.I.val.obj (Opposite.op W)).smul
              (E.π.hom.app (Opposite.op W) a')).asHom.hom m')) :=
        squareZero_kernelStalkInclusion_germ E x W hxW _
    _ = TopCat.Presheaf.germ E.A.presheaf W x hxW (a' * E.ι (Opposite.op W) m') :=
        DFunLike.congr_arg
          (ConcreteCategory.hom (TopCat.Presheaf.germ E.A.presheaf W x hxW))
          (E.smul_lift (Opposite.op W) a' m')
    _ = TopCat.Presheaf.germ E.A.presheaf W x hxW a' *
          TopCat.Presheaf.germ E.A.presheaf W x hxW (E.ι (Opposite.op W) m') :=
        map_mul _ _ _
    _ = TopCat.Presheaf.germ E.A.presheaf U x hx a *
          squareZero_kernelStalkInclusion E x (E.I.presheaf.germ V x hxV m) := by
        rw [ha, ← squareZero_kernelStalkInclusion_germ E x W hxW m', hm]

private theorem squareZero_kernelStalkInclusion_injective
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    Function.Injective (squareZero_kernelStalkInclusion E x) :=
  (ConcreteCategory.bijective_of_isIso
    (commRingStalkToAddCommGrpStalkIso E.A x).inv).1.comp
      (squareZero_stalk_kernel_inclusion_injective E x)

private theorem squareZero_kernelStalkInclusion_range
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X)
    (t : TopCat.Presheaf.stalk (C := CommRingCat.{u}) E.A.presheaf x)
    (ht : ((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom) t = 0) :
    ∃ z, squareZero_kernelStalkInclusion E x z = t := by
  obtain ⟨U, hx, m, hm⟩ := (squareZero_stalk_kernel_eq_range E x t).mp ht
  exact ⟨E.I.presheaf.germ U x hx m,
    (squareZero_kernelStalkInclusion_germ E x U hx m).trans hm⟩

private theorem affine_germ_isLocalization {X : Scheme.{u}}
    (U : X.affineOpens) (y : PrimeSpectrum Γ(X, U.1)) :
    letI := (X.presheaf.germ U.1 (U.2.fromSpec y) (fromSpec_mem U y)).hom.toAlgebra
    IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (U.2.fromSpec y)) := by
  let x := U.2.fromSpec y
  let := (X.presheaf.germ U.1 x (fromSpec_mem U y)).hom.toAlgebra
  let : Algebra Γ(X, U.1) ((Spec Γ(X, U.1)).presheaf.stalk y) :=
    (StructureSheaf.toStalk Γ(X, U.1) y).hom.toAlgebra
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsIso (U.2.fromSpec.stalkMap y) :=
    isIso_stalkMap_of_isOpenImmersion U.2.fromSpec y
  let e : X.presheaf.stalk x ≃+* (Spec Γ(X, U.1)).presheaf.stalk y :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv (asIso (U.2.fromSpec.stalkMap y))
  let e' : X.presheaf.stalk x ≃ₐ[Γ(X, U.1)]
      (Spec Γ(X, U.1)).presheaf.stalk y :=
    { e with commutes' := fromSpec_stalkMap_germ U y }
  exact (IsLocalization.isLocalization_iff_of_algEquiv y.asIdeal.primeCompl e').mpr
    (StructureSheaf.IsLocalization.to_stalk Γ(X, U.1) y)

private theorem squareZero_affine_germ_isLocalization
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.affineOpens) (y : PrimeSpectrum Γ(X, U.1)) :
    let π : E.A.presheaf.obj (Opposite.op U.1) →+* Γ(X, U.1) :=
    (E.π.hom.app (Opposite.op U.1)).hom
    letI := (TopCat.Presheaf.germ E.A.presheaf U.1 (U.2.fromSpec y)
      (fromSpec_mem U y)).hom.toAlgebra
    IsLocalization (y.asIdeal.primeCompl.comap π)
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) E.A.presheaf (U.2.fromSpec y)) := by
  let x := U.2.fromSpec y
  let hx := fromSpec_mem U y
  let π : E.A.presheaf.obj (Opposite.op U.1) →+* Γ(X, U.1) :=
    (E.π.hom.app (Opposite.op U.1)).hom
  let γ := (TopCat.Presheaf.germ E.A.presheaf U.1 x hx).hom
  let g := (X.presheaf.germ U.1 x hx).hom
  let p := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map E.π.hom).hom
  let : IsLocalHom p := squareZero_stalkMap_isLocalHom E x
  let : E.I.IsQuasicoherent := E.quasicoherent
  let := g.toAlgebra
  let : Module (X.presheaf.stalk x) (E.I.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) E.I.val x
  let : Module Γ(X, U.1) (E.I.presheaf.stalk x) :=
    Module.compHom _ g
  let : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk x) :=
    affine_germ_isLocalization U y
  let : Module Γ(X, U.1) (E.I.val.obj (Opposite.op U.1)) :=
    inferInstanceAs (Module Γ(X, U.1) Γ(E.I, U.1))
  apply isLocalization_of_exact_comparison π γ g p (E.ι (Opposite.op U.1))
    (squareZero_kernelStalkInclusion E x) (affineModuleGermMap E.I U y)
    y.asIdeal.primeCompl rfl
  · exact squareZero_sectionMap_surjective_of_affine E U.1 U.2
  · intro a
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply U.1 x hx E.π.hom a
  · intro a ha
    obtain ⟨m, hm, _⟩ := E.exact_kernel (Opposite.op U.1) a ha
    exact ⟨m, hm⟩
  · exact squareZero_kernelStalkInclusion_range E x
  · exact squareZero_kernelStalkInclusion_injective E x
  · exact squareZero_kernelStalkInclusion_germ E x U.1 hx
  · exact E.smul_lift (Opposite.op U.1)
  · exact squareZero_kernelStalkInclusion_smul E x U.1 hx
  · exact affineModuleGermMap_isLocalized E.I U y
  · intro s
    apply (isUnit_map_iff p _).mp
    change IsUnit (p (γ s.val))
    rw [show p (γ s.val) = g (π s.val) from
      TopCat.Presheaf.stalkFunctor_map_germ_apply U.1 x hx E.π.hom s.val]
    exact IsLocalization.map_units (M := y.asIdeal.primeCompl)
      (X.presheaf.stalk x) ⟨π s.val, s.property⟩

private theorem isLocalization_of_ringEquivs
    {R R' T T' : Type*} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (f : R →+* T) (g : R' →+* T') (eR : R ≃+* R') (eT : T ≃+* T')
    (h : ∀ r, g (eR r) = eT (f r)) (M : Submonoid R)
    (hf : letI := f.toAlgebra; IsLocalization M T) :
    letI := g.toAlgebra
    IsLocalization (M.map eR) T' := by
  let := f.toAlgebra
  let := hf
  let := g.toAlgebra
  apply (isLocalization_iff (M.map eR) T').2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, r, hr, rfl⟩
    change IsUnit (g (eR r))
    rw [h]
    exact (IsLocalization.map_units T ⟨r, hr⟩).map eT.toRingHom
  · intro t
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj M (eT.symm t)
    refine ⟨⟨eR r, ⟨eR s.val, ⟨s.val, s.property, rfl⟩⟩⟩, ?_⟩
    change t * g (eR s.val) = g (eR r)
    rw [h, h, ← eT.apply_symm_apply t, ← map_mul]
    exact congrArg eT hs
  · intro a b hab
    have he : f (eR.symm a) = f (eR.symm b) := by
      apply eT.injective
      rw [← h, ← h, eR.apply_symm_apply, eR.apply_symm_apply]
      exact hab
    obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq (M := M) he
    refine ⟨⟨eR s.val, ⟨s.val, s.property, rfl⟩⟩, ?_⟩
    simpa only [map_mul, eR.apply_symm_apply] using congrArg eR hs

private theorem toΓSpec_stalkMap_isIso_of_isLocalization
    (T : LocallyRingedSpace.{u}) (x : T)
    (M : Submonoid (T.presheaf.obj (Opposite.op ⊤)))
    (hM : letI := (T.presheaf.Γgerm x).hom.toAlgebra;
      IsLocalization M (T.presheaf.stalk x)) : IsIso (T.toΓSpec.stalkMap x) := by
  let R := T.presheaf.obj (Opposite.op ⊤)
  let p : PrimeSpectrum R := T.toΓSpecFun x
  let := (T.presheaf.Γgerm x).hom.toAlgebra
  let := hM
  have hN : IsLocalization p.asIdeal.primeCompl (T.presheaf.stalk x) :=
    IsLocalization.of_le M p.asIdeal.primeCompl
      (fun r hr => (T.notMem_prime_iff_unit_in_stalk r x).mpr
        (IsLocalization.map_units (T.presheaf.stalk x) ⟨r, hr⟩))
      (fun r hr => (T.notMem_prime_iff_unit_in_stalk r x).mp hr)
  let := hN
  let : Algebra R ((Spec R).presheaf.stalk p) :=
    (StructureSheaf.toStalk R p).hom.toAlgebra
  let : IsLocalization p.asIdeal.primeCompl ((Spec R).presheaf.stalk p) :=
    StructureSheaf.IsLocalization.to_stalk R p
  let e := IsLocalization.algEquiv p.asIdeal.primeCompl
    ((Spec R).presheaf.stalk p) (T.presheaf.stalk x)
  let q : (Spec R).presheaf.stalk p →+* T.presheaf.stalk x :=
    (T.toΓSpec.stalkMap x).hom
  have he : q = e.toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext r
    exact (locallyRingedSpace_toΓSpec_stalk_germ T x r).trans (e.commutes r).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective q
  rw [he]
  exact e.bijective

private theorem squareZero_affineChartToSpec_isIso
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (thickenedAffineChartToSpec E U) := by
  apply squareZero_affineChartToSpec_isIso_of_stalkMap_isIso E U hU
  intro x
  let y := hU.primeIdealOf x
  have hy : hU.fromSpec y = U.ι x := hU.fromSpec_primeIdealOf x
  have hx := squareZero_affine_germ_isLocalization E ⟨U, hU⟩ y
  have hx' : let := (TopCat.Presheaf.germ E.A.presheaf U (U.ι x) x.2).hom.toAlgebra;
      IsLocalization (y.asIdeal.primeCompl.comap (E.π.hom.app (Opposite.op U)).hom)
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) E.A.presheaf (U.ι x)) := by
    let P : X → Prop := fun z => ∀ hz : z ∈ U,
      let := (TopCat.Presheaf.germ E.A.presheaf U z hz).hom.toAlgebra
      IsLocalization (y.asIdeal.primeCompl.comap (E.π.hom.app (Opposite.op U)).hom)
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) E.A.presheaf z)
    have hp : P (hU.fromSpec y) := fun _ => hx
    exact (hy ▸ hp) x.2
  let T := thickenedAffineChart E U
  let eR : (E.A.presheaf.obj (Opposite.op U)) ≃+* T.presheaf.obj (Opposite.op ⊤) :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (E.A.presheaf.mapIso (eqToIso U.ι_image_top).op)
  let eT : TopCat.Presheaf.stalk (C := CommRingCat.{u}) E.A.presheaf (U.ι x) ≃+*
      T.presheaf.stalk x :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv
      ((thickenedLocallyRingedSpace E).restrictStalkIso U.ι.isOpenEmbedding x).symm
  let M := y.asIdeal.primeCompl.comap (E.π.hom.app (Opposite.op U)).hom
  apply toΓSpec_stalkMap_isIso_of_isLocalization T x (M.map eR)
  apply isLocalization_of_ringEquivs (TopCat.Presheaf.germ E.A.presheaf U (U.ι x) x.2).hom
    (T.presheaf.Γgerm x).hom eR eT ?_ M hx'
  intro a
  apply ((ConcreteCategory.bijective_of_isIso
    ((thickenedLocallyRingedSpace E).restrictStalkIso U.ι.isOpenEmbedding x).hom).1)
  change (((thickenedLocallyRingedSpace E).restrictStalkIso
    U.ι.isOpenEmbedding x).hom) (T.presheaf.Γgerm x (eR a)) = _
  refine Eq.trans (thickenedAffineChart_restrictStalkIso_germ E U x (eR a)) ?_
  change TopCat.Presheaf.germ E.A.presheaf _ (U.ι x) _
    (E.A.presheaf.map (eqToHom U.ι_image_top).op a) = _
  refine Eq.trans (TopCat.Presheaf.germ_res_apply E.A.presheaf
    (eqToHom U.ι_image_top) (U.ι x) _ a) ?_
  exact (ConcreteCategory.congr_hom
    ((thickenedLocallyRingedSpace E).restrictStalkIso
      U.ι.isOpenEmbedding x).inv_hom_id _).symm

private noncomputable def squareZeroExtensionScheme
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (hchart : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (thickenedAffineChartToSpec E U)) : Scheme.{u} := by
  refine {
    toLocallyRingedSpace := thickenedLocallyRingedSpace E
    local_affine := ?_ }
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hiso : IsIso (thickenedAffineChartToSpec E U) := hchart U hU
  exact ⟨⟨U, hxU⟩,
    LocallyRingedSpace.Γ.obj (Opposite.op (thickenedAffineChart E U)),
    ⟨@CategoryTheory.asIso _ _ _ _ (thickenedAffineChartToSpec E U) hiso⟩⟩

private noncomputable def squareZeroExtensionImmersion
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (hchart : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (thickenedAffineChartToSpec E U)) :
    X ⟶ squareZeroExtensionScheme E hchart :=
  Scheme.Hom.mk (canonicalInclusionLocallyRingedSpace E)

private theorem squareZeroExtensionImmersion_isClosedImmersion
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (hchart : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (thickenedAffineChartToSpec E U)) :
    IsClosedImmersion (squareZeroExtensionImmersion E hchart) where
  isClosedEmbedding := by
    change Topology.IsClosedEmbedding (fun x : X => x)
    exact Homeomorph.isClosedEmbedding (Homeomorph.refl X)
  stalkMap_surjective x := by
    change Function.Surjective
      (((canonicalInclusionLocallyRingedSpace E).stalkMap x).hom)
    rw [canonicalInclusionLocallyRingedSpace_stalkMap]
    exact squareZero_stalkMap_surjective E x

private theorem squareZeroExtensionImmersion_app
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (hchart : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (thickenedAffineChartToSpec E U)) (U : X.Opens) :
    ((squareZeroExtensionImmersion E hchart).app U).hom =
      ((E.π.hom.app (Opposite.op U)).hom) := by
  rfl

private theorem squareZeroExtensionImmersion_ker_sq
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (hchart : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (thickenedAffineChartToSpec E U)) :
    (squareZeroExtensionImmersion E hchart).ker ^ 2 = ⊥ := by
  let i := squareZeroExtensionImmersion E hchart
  let Y := squareZeroExtensionScheme E hchart
  let : IsClosedImmersion i := squareZeroExtensionImmersion_isClosedImmersion E hchart
  let : QuasiCompact i := inferInstance
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens => U) (iSup_affineOpens_eq_top Y)
  intro U
  change (i.ker.ideal U) ^ 2 = ⊥
  rw [Scheme.Hom.ker_apply i U]
  rw [pow_two]
  apply le_antisymm
  · have hker : ∀ a ∈ RingHom.ker (i.app (U : Y.Opens)).hom,
        ∃ x, E.ι (Opposite.op (U : Y.Opens)) x = a := fun a ha => by
      have hπ : (E.π.hom.app (Opposite.op (U : Y.Opens))).hom a = 0 := by
        rw [← squareZeroExtensionImmersion_app E hchart (U : Y.Opens)]
        exact ha
      obtain ⟨x, hx, -⟩ := E.exact_kernel (Opposite.op (U : Y.Opens)) a hπ
      exact ⟨x, hx⟩
    apply Ideal.mul_le.mpr
    intro a ha b hb
    obtain ⟨x, rfl⟩ := hker a ha
    obtain ⟨y, rfl⟩ := hker b hb
    exact E.square_zero (Opposite.op (U : Y.Opens)) x y
  · exact bot_le

/-- A scheme realizing the specified extension as a first-order thickening over `S`. -/
public structure Realization {X S : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) where
  ambient : Scheme.{u}
  sheafedIso : ambient.toSheafedSpace ≅ thickenedSpace X E.A
  immersion : X ⟶ ambient
  toBase : ambient ⟶ S
  immersion_isFirstOrder : Stacks.Thickenings.IsFirstOrderThickening immersion
  over_base : immersion ≫ toBase = f
  inclusion_eq : immersion.toLRSHom.toShHom ≫ sheafedIso.hom = E.inclusion
  toBase_eq : sheafedIso.inv ≫ toBase.toLRSHom.toShHom = E.toBase

private theorem squareZeroExtension_realization_of_chart_isos
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (hchart : ∀ (U : X.Opens), IsAffineOpen U →
      IsIso (thickenedAffineChartToSpec E U)) : Nonempty (Realization E) := by
  let Y := squareZeroExtensionScheme E hchart
  let i := squareZeroExtensionImmersion E hchart
  let j : Y ⟶ S := Scheme.Hom.mk (thickenedToBaseLocallyRingedSpace E)
  have hover : i ≫ j = f := by
    apply congrArg Scheme.Hom.mk
    apply LocallyRingedSpace.Hom.ext'
    exact congrArg (fun q => q.hom) (canonicalInclusionSheafedSpace_toBase E)
  have hi : Stacks.Thickenings.IsFirstOrderThickening i :=
    ⟨squareZeroExtensionImmersion_isClosedImmersion E hchart,
      squareZeroExtensionImmersion_ker_sq E hchart⟩
  refine ⟨{
    ambient := Y
    sheafedIso := Iso.refl _
    immersion := i
    toBase := j
    immersion_isFirstOrder := hi
    over_base := hover
    inclusion_eq := ?_
    toBase_eq := ?_ }⟩
  · change (canonicalInclusionLocallyRingedSpace E).toShHom = E.inclusion
    exact canonicalInclusionSheafedSpace_eq E
  · rfl

/-- A square-zero extension with quasi-coherent kernel gives a first-order thickening. -/
@[stacks 05YV "construction from a square-zero extension"]
public theorem squareZeroExtension_realization {X S : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) : Nonempty (Realization E) :=
  squareZeroExtension_realization_of_chart_isos E fun U hU =>
    squareZero_affineChartToSpec_isIso E U hU

end Stacks.Thickenings
