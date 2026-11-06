module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.CharacteristicZero
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.EssentiallySurjective
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import Mathlib.CategoryTheory.Galois.Decomposition

/-!
# Injectivity of a specialization map from the descent of Galois covers alone

`AlgebraicGeometry.injective_etaleFundamentalGroupMap_of_essSurj` makes
`π₁(X) ⟶ π₁(Y)` injective out of the essential surjectivity of base change on *all* finite étale
covers. This file weakens the input to the Galois covers.

The reason is that an element of `π₁(X, x)` is trivial as soon as it acts trivially on the
geometric fibre of every Galois cover: a point of the fibre of an arbitrary cover `V` is the image
of a point of the fibre of a Galois cover `A` under some `A ⟶ V`
(`CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber`), and naturality carries the
triviality down. So only the Galois covers need to be in the essential image of base change, and
the component at a cover isomorphic to one in the essential image is read off that cover by
naturality against the isomorphism.

This is the form in which the remaining input of [Stacks, Tag 0C0Q] is produced: the extension
theorems for a cover of the generic fibre over a normal base
(`AlgebraicGeometry.FiniteEtaleGaloisCover.exists_extension_of_genericFiber_of_isNoetherian`,
[Stacks, Tag 0EYJ]) extend *Galois* covers, so the hypothesis they can discharge is the one below
and not the essential surjectivity of base change.

## Main results

* `AlgebraicGeometry.injective_etaleFundamentalGroupMap_of_essImage_isGalois` — the homomorphism
  of étale fundamental groups induced by a morphism along which every Galois finite étale cover of
  the source is a base change is injective.
* `AlgebraicGeometry.injective_of_essImage_isGalois_of_specializationMapEquation` — the
  specialization-map form.
* `AlgebraicGeometry.injective_specializationMap_of_essImage_isGalois` — the same in the shape in
  which the construction of a specialization map presents its data.

## References

* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Injectivity of the induced homomorphism -/

/-- **An element of `π₁` acting trivially on every Galois cover is trivial.** A point of the
geometric fibre of an arbitrary finite étale cover `V` is the image of a point of the fibre of a
Galois cover under a morphism to `V`, and naturality transports the triviality. -/
theorem eq_one_of_app_isGalois_eq_id {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)
    (γ : EtaleFundamentalGroup X x)
    (hA : ∀ A : FiniteEtaleOver X, CategoryTheory.PreGaloisCategory.IsGalois A →
      γ.asIso.hom.app A = 𝟙 _) :
    γ = 1 := by
  apply Aut.ext
  apply Iso.ext
  ext V p
  obtain ⟨A, f, a, hgal, ha⟩ :=
    exists_hom_from_galois_of_fiber (finiteEtaleFiberFintypeFunctor X x) V p
  have hp : (finiteEtaleFiberFunctor x).map f a = p := ha
  have hm : (finiteEtaleFiberFunctor x).map f ≫ γ.asIso.hom.app V
      = (finiteEtaleFiberFunctor x).map f := by
    rw [γ.asIso.hom.naturality f, hA A hgal, Category.id_comp]
  show (ConcreteCategory.hom (γ.asIso.hom.app V)) p = p
  rw [← hp]
  exact ConcreteCategory.congr_hom hm a

/-- **A morphism along which every Galois cover of the source is a base change induces an
injective homomorphism of étale fundamental groups.** Let `f : X ⟶ Y` be a morphism of connected
schemes and `x` a geometric point of `X`. If every finite étale cover of `X` which is a Galois
object of `FÉt_X` is isomorphic to the base change of a finite étale cover of `Y`, then
`π₁(X, x) ⟶ π₁(Y, f ∘ x)` is injective.

The induced homomorphism is the action on automorphism groups of precomposition with the base
change functor, followed by conjugation by the fibre projections. An element in the kernel
restricts to the identity on every cover in the essential image of base change, hence — by
naturality against the given isomorphism — on every Galois cover, hence is trivial by
`AlgebraicGeometry.eq_one_of_app_isGalois_eq_id`. -/
theorem injective_etaleFundamentalGroupMap_of_essImage_isGalois {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X)
    (hgal : ∀ A : FiniteEtaleOver X, CategoryTheory.PreGaloisCategory.IsGalois A →
      ∃ B : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange f).obj B ≅ A)) :
    Function.Injective (etaleFundamentalGroupMap f x) := by
  let W := (Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
    (finiteEtaleBaseChange f)
  have key : ∀ γ : Aut (finiteEtaleFiberFunctor x),
      W.mapAut (finiteEtaleFiberFunctor x) γ = 1 → γ = 1 := by
    intro γ hone
    refine eq_one_of_app_isGalois_eq_id x γ fun A hA ↦ ?_
    obtain ⟨B, ⟨e⟩⟩ := hgal A hA
    have hnat := γ.asIso.hom.naturality e.hom
    rw [show γ.asIso.hom.app ((finiteEtaleBaseChange f).obj B) = 𝟙 _ from
      NatTrans.congr_app (congrArg (fun a ↦ a.asIso.hom) hone) B, Category.id_comp] at hnat
    exact ((finiteEtaleFiberFunctor x).mapIso e).cancel_iso_hom_left _ _ |>.mp
      (hnat.trans (Category.comp_id _).symm)
  have hcomp : (etaleFundamentalGroupMap f x :
      EtaleFundamentalGroup X x → EtaleFundamentalGroup Y (x.map f)) =
      (finiteEtaleFiberProjectionIso f x).conjAut ∘ W.mapAut (finiteEtaleFiberFunctor x) := rfl
  rw [hcomp]
  exact (finiteEtaleFiberProjectionIso f x).conjAut.injective.comp
    ((injective_iff_map_eq_one _).mpr key)

/-! ### Injectivity of a specialization map -/

/-- **A specialization map is injective when every Galois cover of the geometric generic fibre is
a base change.** The hypothesis of
`AlgebraicGeometry.injective_of_essSurj_of_specializationMapEquation` weakened to the Galois
covers. -/
theorem injective_of_essImage_isGalois_of_specializationMapEquation {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [GeometricallyConnected f] {s' s : GeometricPoint S}
    {T : Scheme.{u}} (g : T ⟶ S) [ConnectedSpace ↥(pullback f g)]
    (p' : s'.source ⟶ T) (hp' : p' ≫ g = s'.hom)
    (p : s.source ⟶ T) (hp : p ≫ g = s.hom)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hgal : ∀ A : FiniteEtaleOver (fiberOverGeometricPoint f s'),
      CategoryTheory.PreGaloisCategory.IsGalois A →
      ∃ B : FiniteEtaleOver (pullback f g),
        Nonempty ((finiteEtaleBaseChange
          (fiberOverGeometricPointMap f s' g p' hp')).obj B ≅ A))
    (t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' g p' hp')) ≅
      finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s g p hp)))
    (hform : ∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s g p hp) x (sp γ)
      = etaleFundamentalGroupMulEquiv t
        (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' g p' hp') x' γ)) :
    Function.Injective sp := by
  intro γ₁ γ₂ hγ
  refine injective_etaleFundamentalGroupMap_of_essImage_isGalois
    (fiberOverGeometricPointMap f s' g p' hp') x' hgal
    ((etaleFundamentalGroupMulEquiv t).injective ?_)
  rw [← hform γ₁, ← hform γ₂, hγ]

/-- **Injectivity of a specialization map presented by a strict henselization, from the descent of
Galois covers.** The statement of
`AlgebraicGeometry.injective_specializationMap_of_essSurj` with its essential surjectivity
hypothesis weakened: only the finite étale covers of the geometric generic fibre which are Galois
objects need to be base changes of covers of `X_A`.

This is the shape the extension theorems for Galois covers of a generic fibre can discharge. -/
theorem injective_specializationMap_of_essImage_isGalois {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A]
    (p' : s'.source ⟶ Spec (.of A))
    (hp' : p' ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s'.hom)
    (p : s.source ⟶ Spec (.of A))
    (hp : p ≫ specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A = s.hom)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hgal : ∀ B : FiniteEtaleOver (fiberOverGeometricPoint f s'),
      CategoryTheory.PreGaloisCategory.IsGalois B →
      ∃ C : FiniteEtaleOver
          (pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)),
        Nonempty ((finiteEtaleBaseChange
          (fiberOverGeometricPointMap f s' _ p' hp')).obj C ≅ B)) :
    letI : ConnectedSpace
        ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
      connectedSpace_pullback_spec_of_isProper f A _
    ∀ t : finiteEtaleFiberFunctor (x'.map (fiberOverGeometricPointMap f s' _ p' hp')) ≅
        finiteEtaleFiberFunctor (x.map (fiberOverGeometricPointMap f s _ p hp)),
      (∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap f s _ p hp) x (sp γ)
          = etaleFundamentalGroupMulEquiv t
            (etaleFundamentalGroupMap (fiberOverGeometricPointMap f s' _ p' hp') x' γ)) →
        Function.Injective sp := by
  let : ConnectedSpace
      ↥(pullback f (specStalkAlgebraHom S (s.hom (closedPoint s.residueField)) A)) :=
    connectedSpace_pullback_spec_of_isProper f A _
  exact fun t hform ↦ injective_of_essImage_isGalois_of_specializationMapEquation f _ p' hp' p hp
    x' x sp hgal t hform

/-- **Injectivity of a specialization map from the descent of Galois covers to `X` itself.**
Let `f : X ⟶ S` be proper with geometrically connected fibres, let `s' ⇝ s` be a specialization
of points of `S` and let `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` be a specialization map. If every finite
étale cover of the geometric fibre `X_{s̄'}` which is a Galois object of `FÉt_{X_{s̄'}}` is
isomorphic to the base change along `X_{s̄'} ⟶ X` of a finite étale cover of `X`, then `sp` is
injective.

No strict henselization appears in the hypothesis: the geometric point `s̄'` factors through the
strict henselization `Spec A` used to build `sp`, so `X_{s̄'} ⟶ X` factors as
`X_{s̄'} ⟶ X_A ⟶ X` and a cover of `X` pulled back to `X_A` restricts on `X_{s̄'}` to the pullback
of the original, by `AlgebraicGeometry.finiteEtaleBaseChangeComp`. So descending to `X` is
stronger than descending to `X_A`, which is what
`AlgebraicGeometry.injective_specializationMap_of_essImage_isGalois` consumes.

This is the shape in which [Stacks, Tag 0C0Q] needs its remaining input: over a strictly henselian
discrete valuation ring with algebraically closed residue field of characteristic zero, every
Galois finite étale cover of the geometric generic fibre `Y_{η̄}` is the base change of a finite
étale cover of `Y`. -/
theorem injective_isSpecializationMap_of_essImage_isGalois {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hgal : ∀ A : FiniteEtaleOver (fiberOverGeometricPoint f s'),
      CategoryTheory.PreGaloisCategory.IsGalois A →
      ∃ B : FiniteEtaleOver X,
        Nonempty ((finiteEtaleBaseChange (pullback.fst f s'.hom)).obj B ≅ A)) :
    Function.Injective sp := by
  obtain ⟨A, _, _, _, -, p', hp', p, hp, -, _, -, t, hform⟩ := hsp
  refine injective_of_essImage_isGalois_of_specializationMapEquation f _ p' hp' p hp x' x sp
    (fun B hB ↦ ?_) t hform
  obtain ⟨C, ⟨e⟩⟩ := hgal B hB
  exact ⟨(finiteEtaleBaseChange (pullback.fst f _)).obj C,
    ⟨((finiteEtaleBaseChangeComp (fiberOverGeometricPointMap f s' _ p' hp')
      (pullback.fst f _) (pullback.fst f s'.hom) (pullback.lift_fst _ _ _).symm).app C).symm ≪≫ e⟩⟩

/-! ### The residual input of Tag 0C0Q, on Galois covers of the geometric generic fibre -/

/-- **Stacks Project, Tag 0C0Q, granted the descent of Galois covers of the geometric generic
fibre over a strictly henselian discrete valuation ring (`Hgal`).** Let `f : X ⟶ S` be a smooth
proper morphism with geometrically connected fibres, let `s' ⇝ s` be a specialization realized by
a specialization map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, and suppose the characteristic of `κ(s)` is
zero. If, for every strictly henselian discrete valuation ring `R` whose residue field is
algebraically closed **of characteristic zero** and every smooth proper `h : Y ⟶ Spec R` with
geometrically connected fibres, every Galois finite étale cover of the geometric generic fibre
`Y_{η̄}` is the base change along `Y_{η̄} ⟶ Y` of a finite étale cover of `Y`, then `sp` is
bijective.

This is `bijective_isSpecializationMap_of_ringChar_zero_of_forall_isDiscreteValuationRing` with
its input rewritten through `AlgebraicGeometry.injective_isSpecializationMap_of_essImage_isGalois`.
Compared with that statement, the input no longer mentions the étale fundamental group, a
specialization map or a strict henselization, and it is restricted to the Galois covers — which is
the class the extension theorems for a cover of a generic fibre ([Stacks, Tag 0EYJ],
`AlgebraicGeometry.FiniteEtaleGaloisCover.exists_extension_of_genericFiber_of_isNoetherian`)
produce.

The residue characteristic of `R` is part of `Hgal` and must be: the descent of covers of the
geometric generic fibre is *false* over a strictly henselian discrete valuation ring of residue
characteristic `p > 0`, since that is exactly the failure of injectivity of the specialization map
which restricts [Stacks, Tag 0C0R] to the maximal prime-to-`p` quotients. The reduction forces
the residue characteristic of the ring it produces to be zero and hands that equation on, so
`Hgal` is asked only of the rings for which it can hold.

**No `@[stacks 0C0Q]` attribute is attached**: `Hgal` is an input, not a theorem. -/
theorem bijective_isSpecializationMap_of_ringChar_zero_of_forall_essImage_isGalois
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0)
    (Hgal : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        [StrictlyHenselianLocalRing R] [IsAlgClosed (ResidueField R)]
        (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h]
        [GeometricallyConnected h] (η : GeometricPoint (Spec (.of R)))
        (A : FiniteEtaleOver (fiberOverGeometricPoint h η)),
        ringChar ((Spec (.of R)).residueField (closedPoint R)) = 0 →
          η.hom default = genericPoint (Spec (.of R)) →
            CategoryTheory.PreGaloisCategory.IsGalois A →
              ∃ B : FiniteEtaleOver Y,
                Nonempty ((finiteEtaleBaseChange (pullback.fst h η.hom)).obj B ≅ A)) :
    Function.Bijective sp := by
  refine bijective_isSpecializationMap_of_ringChar_zero_of_forall_isDiscreteValuationRing f s' s
    x' x sp hsp hchar ?_
  intro R _ _ _ _ _ Y h _ _ _ η o yη yo spR hη ho hcharR hspR
  exact injective_isSpecializationMap_of_essImage_isGalois h η o yη yo spR hspR
    fun A hA ↦ Hgal R Y h η A (ho ▸ hcharR) hη hA

end AlgebraicGeometry

end
