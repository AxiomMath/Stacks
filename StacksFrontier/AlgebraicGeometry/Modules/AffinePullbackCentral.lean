module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsCentral
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.CategoryTheory.Functor.NatEndCentral

/-!
# Natural endomorphisms of the inverse image along a morphism of affine schemes

For a morphism `g : X ⟶ Y` of affine schemes, every natural endomorphism of the inverse image
`g^*` on quasi-coherent `𝒪_Y`-modules commutes with every morphism `g^*M ⟶ g^*N` of
`𝒪_X`-modules, also with those that are not inverse images. Under `QCoh(Spec A) ≃ Mod(A)` the
inverse image along `Spec B ⟶ Spec A` is extension of scalars, whose natural endomorphisms are
multiplications by elements of `B` (`ModuleCat.ExtendScalars.natTrans_app_eq_smul`).

## Main results

* `ModuleCat.extendScalars_natEndCentral`: extension of scalars has central natural
  endomorphisms.
* `AlgebraicGeometry.Scheme.Modules.natEndCentral_pullback_of_isAffine`: so has the inverse
  image along a morphism of affine schemes, restricted to quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory

universe u

/-- Extension of scalars along a homomorphism of commutative rings has central natural
endomorphisms. -/
theorem ModuleCat.extendScalars_natEndCentral {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : (ModuleCat.extendScalars.{u, u, u} f).NatEndCentral := fun δ M N φ ↦
  ModuleCat.ExtendScalars.natTrans_app_comp_eq (P := ⊤) trivial
    (Functor.whiskerLeft (⊤ : ObjectProperty (ModuleCat.{u} A)).ι δ)
    (M := ⟨M, trivial⟩) (N := ⟨N, trivial⟩) φ

namespace AlgebraicGeometry.Scheme.Modules

/-- The inverse image along the morphism of spectra of a ring homomorphism, restricted to
quasi-coherent modules, has central natural endomorphisms. -/
theorem natEndCentral_pullback_specMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (Spec.map f)).NatEndCentral := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  have hP : ∀ M : ModuleCat.{u} R, P ((tilde.functor R).obj M) := fun M => by
    change (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) _
    rw [← essImage_tilde]
    exact (tilde.functor R).obj_mem_essImage M
  let e : ModuleCat.{u} R ⥤ P.FullSubcategory := P.lift (tilde.functor R) hP
  have : e.EssSurj := ⟨fun N => by
    have hN : (tilde.functor R).essImage N.obj := by
      rw [essImage_tilde]
      exact N.property
    exact ⟨hN.witness, ⟨P.fullyFaithfulι.preimageIso (X := e.obj hN.witness) (Y := N) hN.getIso⟩⟩⟩
  exact Functor.NatEndCentral.of_comp (e := e) <| Functor.NatEndCentral.of_iso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (P.liftCompιIso (tilde.functor R) hP) _ ≪≫ pullbackTildeIso R S f)
    ((ModuleCat.extendScalars_natEndCentral f.hom).comp tilde.fullyFaithfulFunctor)

/-- **The inverse image along a morphism of affine schemes, restricted to quasi-coherent
modules, has central natural endomorphisms**: every natural endomorphism of `g^*` commutes with
every morphism `g^*M ⟶ g^*N`. -/
theorem natEndCentral_pullback_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) :
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙
      Scheme.Modules.pullback g).NatEndCentral := by
  let PY := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let PS := SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf
  have hP : ∀ M : PS.FullSubcategory, PY ((Scheme.Modules.pullback Y.isoSpec.hom).obj M.obj) :=
    fun M => Stacks.Modules.isQuasicoherent_pullback _ _ M.property
  let e : PS.FullSubcategory ⥤ PY.FullSubcategory :=
    PY.lift (PS.ι ⋙ Scheme.Modules.pullback Y.isoSpec.hom) hP
  have : e.EssSurj := ⟨fun N =>
    let M : PS.FullSubcategory := ⟨(Scheme.Modules.pullback Y.isoSpec.inv).obj N.obj,
      Stacks.Modules.isQuasicoherent_pullback _ _ N.property⟩
    ⟨M, ⟨PY.fullyFaithfulι.preimageIso (X := e.obj M) (Y := N)
      ((pullbackEquivOfIso Y.isoSpec).counitIso.app N.obj)⟩⟩⟩
  refine Functor.NatEndCentral.of_comp (e := e) <| Functor.NatEndCentral.of_iso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (PY.liftCompιIso _ hP) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft PS.ι (Scheme.Modules.pullbackComp g Y.isoSpec.hom ≪≫
        Scheme.Modules.pullbackCongr (Scheme.isoSpec_hom_naturality g).symm ≪≫
        (Scheme.Modules.pullbackComp X.isoSpec.hom (Spec.map g.appTop)).symm) ≪≫
      (Functor.associator _ _ _).symm) ?_
  exact (natEndCentral_pullback_specMap g.appTop).comp
    (pullbackEquivOfIso X.isoSpec).fullyFaithfulFunctor

end AlgebraicGeometry.Scheme.Modules

end
