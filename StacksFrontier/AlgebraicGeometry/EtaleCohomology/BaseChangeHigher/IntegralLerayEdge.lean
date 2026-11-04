module

public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralRelativeLeray
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedDirectImagePasting
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting

/-!
# The relative Leray identification is the edge morphism of the composite

`Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral` identifies `π_* ⋙ R^q g_*` with
`R^q (π ≫ g)_*` for an integral `π`, in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`. The derived pasting law along the direct image legs,
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`, lives in the
bounded below derived category, where the comparison of the two composite direct images is
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso'`. This file identifies the two:
read through the comparison `Stacks.DerivedIndexing.rightDerivedIso` of the two indexings of the
right derived functors, the relative Leray identification is the degree-`q` cohomology of the
canonical map `(π_*ℱ)[0] ⟶ Rπ_*(ℱ[0])` followed by that comparison — in other words it is the
degreewise comparison `Stacks.DerivedIndexing.rightDerivedPlusEdge` of the composite.

The identification holds for any exact functor preserving injective objects
(`Stacks.DerivedIndexing.collapseIso_comp_rightDerivedIso`); integrality of `π` makes `π_*`
exact.

## Main results

* `Stacks.Cohomology.RightDerivedEdge.edge_eq_compRightDerivedNatIso_inv`: **the collapse
  isomorphism of [Stacks, Tag 015Z] is the edge morphism.** For `L` exact and preserving
  injective objects, the inverse of
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` is
  `Stacks.Cohomology.RightDerivedEdge.edge`. Both are read off a comparison of injective
  resolutions, and at `L` applied to the chosen resolution of `ℱ` the comparison may be taken to
  be the identity.
* `Stacks.DerivedIndexing.collapseIso_comp_rightDerivedIso`: **the generic identification**, for
  an isomorphism `c : L ⋙ G ≅ H` of additive functors with `L` exact and preserving injective
  objects.
* `Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral_hom_app_comp_rightDerivedIso`:
  **the étale instance**, at `π_*` and `g_*` for an integral `π`.
* `Stacks.EtaleCohomology.relativeLeray_comp_baseChangeSourceIso`: **the source side of the
  degreewise descent of the direct-image pasting law.** The relative Leray identification,
  read through the identification `Stacks.EtaleCohomology.baseChangeSourceIso` of the rectangle's
  source, is the identification of the lower square's source followed by the degree-`q`
  cohomology of the inverse image of the derived comparison of the composite direct images.
* `CategoryTheory.Functor.rightDerivedPlusCompTrans_eq`,
  `CategoryTheory.Functor.rightDerivedPlusCompIso_eq`,
  `CategoryTheory.Functor.rightDerivedFunctorPlusNatTrans_eq`: the three places where this
  development carries two spellings of one comparison of right derived functors on bounded below
  derived categories. Each is a definitional identity.

## Implementation notes

*Why the edge morphism is the collapse isomorphism.*
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` computes the edge morphism from *any*
augmentation-preserving comparison `φ : J ⟶ L(I)` of injective resolutions, `I` of `ℱ` and `J` of
`Lℱ`. For `L` exact and preserving injectives, `L(I)` is itself an injective resolution of `Lℱ`
— that is `Stacks.Cohomology.CompositeRightDerived.mapInjRes` — so `φ` may be taken to be the
identity, and what is left of the edge morphism is exactly the pair of resolution comparisons out
of which `compRightDerivedNatIso` is built.

*Why the algebra of the source side is on variables.*
`Stacks.EtaleCohomology.srcChase` is the rearrangement that turns the identification above and
one naturality square into the source side of the descent. Its morphisms are components of
comparisons of right derived functors at sheaves on small étale sites, where the source of one
factor and the target of the next agree only after unfolding
`CategoryTheory.Functor.rightDerivedFunctorPlus`; a `rw`-driven rearrangement there builds terms
that are not type-correct at the transparency `rw` matches at. The same is true of
`Stacks.DerivedIndexing.assocMap`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe w w' w'' v v' v'' u u' u''

namespace Stacks.Cohomology.RightDerivedEdge

/-- **The collapse isomorphism of [Stacks, Tag 015Z] is the edge morphism.** For an exact
`P : 𝒜 ⥤ ℬ` preserving injective objects and an additive `Q : ℬ ⥤ 𝒟`, the inverse of
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` — which identifies
`R ⁿ(Q ∘ P)` with `P ⋙ R ⁿQ` by computing both on the chosen injective resolution of `ℱ` and its
image under `P` — is `Stacks.Cohomology.RightDerivedEdge.edge`, the edge morphism of the pair
`(P, Q)`.

`Stacks.Cohomology.RightDerivedEdge.edge_app_eq` reads the edge morphism off any
augmentation-preserving comparison of injective resolutions; here `P` applied to the chosen
resolution of `ℱ` *is* an injective resolution of `Pℱ`, so the identity serves as that
comparison. -/
public theorem edge_eq_compRightDerivedNatIso_inv {A : Type*} {B : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* D] [Abelian A] [Abelian B] [Abelian D]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (P : A ⥤ B) (Q : B ⥤ D) [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] [P.PreservesInjectiveObjects]
    (n : ℕ) :
    edge P Q n =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).inv := by
  refine NatTrans.ext (funext fun X => ?_)
  have hι : (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).ι.f 0 = P.map ((injectiveResolution X).ι.f 0) := by
    dsimp [Stacks.Cohomology.CompositeRightDerived.mapInjRes]
    simp
  rw [edge_app_eq P Q n (injectiveResolution X)
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes P (injectiveResolution X)) (𝟙 _)
    ((Category.comp_id _).trans hι)]
  simp only [Functor.comp_obj, CompositeRightDerived.mapInjRes, CategoryTheory.Functor.map_id,
    CompositeRightDerived.compRightDerivedNatIso, eqToIso_refl, Iso.refl_trans,
    NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv, Iso.cancel_iso_hom_left]
  exact (congrArg (fun z => z ≫
      ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).inv)
    (HomologicalComplex.homologyMap_id _ n)).trans (Category.id_comp _)

end Stacks.Cohomology.RightDerivedEdge

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Two spellings of the comparison transformation, and of the invariance comparison -/

section Spellings

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w''} C]
  [EnoughInjectives A] [EnoughInjectives B]

/-- **The two spellings of the canonical transformation `t : R(Q ∘ P) ⟶ RQ ∘ RP`** of
[Stacks, Tag 05T2] agree. `Stacks.DerivedIndexing.rightDerivedPlusCompTrans` and
`CategoryTheory.Functor.rightDerivedFunctorPlusComp` are the descents along the unit of
`R(Q ∘ P)` of `Stacks.DerivedIndexing.rightDerivedPlusCompUnit` and of
`CategoryTheory.Functor.rightComparisonUnit`, which are the same transformation. -/
public theorem rightDerivedPlusCompTrans_eq (P : A ⥤ B) (Q : B ⥤ C) [P.Additive] [Q.Additive] :
    Stacks.DerivedIndexing.rightDerivedPlusCompTrans P Q = rightDerivedFunctorPlusComp P Q :=
  rfl

/-- **The two spellings of the composition isomorphism `R(Q ∘ P) ≅ RQ ∘ RP`** of
[Stacks, Tag 015M] agree: both are the canonical transformation, inverted. -/
public theorem rightDerivedPlusCompIso_eq (P : A ⥤ B) (Q : B ⥤ C) [P.Additive] [Q.Additive]
    [P.PreservesInjectiveObjects] :
    Stacks.DerivedIndexing.rightDerivedPlusCompIso P Q =
      rightDerivedFunctorPlusCompIsoOfRightAcyclic P Q
        (fun I hI => rightAcyclic_obj_of_preservesInjectiveObjects P Q I hI) :=
  Iso.ext rfl

omit [EnoughInjectives B] in
/-- **The two spellings of the invariance comparison `RF ≅ RG` of an isomorphism `F ≅ G`**
agree: both are the descent along the units of the degreewise action of the isomorphism. -/
public theorem rightDerivedFunctorPlusNatTrans_eq {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) :
    Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans e.hom =
      (rightDerivedFunctorPlusNatIso e).hom :=
  rfl

end Spellings

end CategoryTheory.Functor

namespace Stacks.DerivedIndexing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Collapse

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]

/-- A functor applied to a threefold composite, with the first two factors bracketed as the
rearrangement below produces them. Stated on variables: the morphisms it is applied to are
components of comparisons of right derived functors, whose sources and targets agree only
definitionally. -/
public theorem assocMap {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {Z₀ Z₁ Z₂ Z₃ : 𝒞} (a : Z₀ ⟶ Z₁) (b : Z₁ ⟶ Z₂) (d : Z₂ ⟶ Z₃) :
    (Φ.map a ≫ Φ.map b) ≫ Φ.map d = Φ.map (a ≫ b ≫ d) := by simp

/-- **The collapse isomorphism of [Stacks, Tag 015Z], read in the `ℤ`-indexing.** Let
`L : 𝒞 ⥤ 𝒟` be exact and preserve injective objects, let `G : 𝒟 ⥤ ℰ` be additive and let
`c : L ⋙ G ≅ H`. The identification `L ⋙ R ⁿG ≅ R ⁿH` obtained from
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` and the invariance of
`CategoryTheory.Functor.rightDerived` under `c`, read through the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the two indexings, is the degree-`q` cohomology of
the canonical map `(Lℱ)[0] ⟶ RL(ℱ[0])` followed by the comparison `RL ⋙ RG ≅ RH` of
[Stacks, Tag 015M].

In other words the collapse isomorphism is
`Stacks.DerivedIndexing.rightDerivedPlusEdge L G q`, transported along `c`; the proof is
`Stacks.Cohomology.RightDerivedEdge.edge_eq_compRightDerivedNatIso_inv` followed by
`Stacks.DerivedIndexing.edge_comp_rightDerivedIso`. -/
public theorem collapseIso_comp_rightDerivedIso (L : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [L.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
    (c : L ⋙ G ≅ H) (q : ℕ) (X : C) :
    ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G q).symm ≪≫
            Functor.rightDerivedIsoOfNatIso c q).hom.app X ≫
        (rightDerivedIso H q).hom.app X =
      (rightDerivedIso G q).hom.app (L.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor E (q : ℤ)).map
          (G.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle L).app X) ≫
            (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives L G H c).hom.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj X)) := by
  have hnat := NatTrans.congr_app (rightDerivedIso_hom_naturality c.hom q) X
  simp only [NatTrans.comp_app] at hnat
  have hiso : (Functor.rightDerivedIsoOfNatIso c q).hom.app X =
      (NatTrans.rightDerived c.hom q).app X := rfl
  have e1 : (rightDerivedPlusCompIso L G).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        (Functor.rightDerivedFunctorPlusNatIso c).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives L G H c).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) := by
    rw [Functor.rightDerivedPlusCompIso_eq,
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom]
    exact (NatTrans.comp_app _ _ _).symm
  have key : (rightDerivedPlusEdge L G (q : ℤ)).app X ≫
        (rightDerivedPlusNatTrans c.hom (q : ℤ)).app X =
      (DerivedCategory.Plus.homologyFunctor E (q : ℤ)).map
        (G.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle L).app X) ≫
          (rightDerivedPlusCompIso L G).inv.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
            (Functor.rightDerivedFunctorPlusNatIso c).hom.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj X)) :=
    (congrArg (fun z => z ≫ (rightDerivedPlusNatTrans c.hom (q : ℤ)).app X)
        (rightDerivedPlusEdge_app L G (q : ℤ) X)).trans
      (assocMap (DerivedCategory.Plus.homologyFunctor E (q : ℤ)) _ _ _)
  rw [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    ← Stacks.Cohomology.RightDerivedEdge.edge_eq_compRightDerivedNatIso_inv, hiso, hnat,
    ← Category.assoc, edge_comp_rightDerivedIso L G q X, Category.assoc, key, e1]
  rfl

end Collapse

end Stacks.DerivedIndexing

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The relative Leray identification across an integral morphism as an edge morphism -/

/-- **The relative Leray identification across an integral morphism is the degreewise comparison
of the composite.** For `π : T' ⟶ T` integral and `g : T ⟶ S` arbitrary, the identification
`π_* ⋙ R^q g_* ≅ R^q(π ≫ g)_*` of
`Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral`, read through the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the injective-resolution and bounded-below
conventions, is the degree-`q` cohomology of the canonical map `(π_*ℱ)[0] ⟶ Rπ_*(ℱ[0])` followed
by the comparison `Rπ_* ⋙ Rg_* ≅ R(π ≫ g)_*` of
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso'`.

This is the generic `Stacks.DerivedIndexing.collapseIso_comp_rightDerivedIso` at `π_*` and `g_*`;
the exactness of `π_*` it consumes is what integrality of `π` provides
(`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom`), and preservation of
injectives is free. -/
public theorem smallEtaleRelativeLerayIsoOfIntegral_hom_app_comp_rightDerivedIso
    {T' T S : Scheme.{u}} (π : T' ⟶ T) (g : T ⟶ S) (hπ : IsIntegralHom π) (q : ℕ)
    (M : Sheaf (smallEtaleTopology T') Ab.{u + 1}) :
    (smallEtaleRelativeLerayIsoOfIntegral π g hπ q).hom.app M ≫
        (Stacks.DerivedIndexing.rightDerivedIso
          (smallEtalePushforwardAb (π ≫ g)) q).hom.app M =
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.app
          ((smallEtalePushforwardAb π).obj M) ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℤ)).map
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.map
              ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
                (smallEtalePushforwardAb π)).app M) ≫
            (smallEtaleDerivedPushforwardAbCompIso' π g (π ≫ g) rfl).hom.app
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallEtaleTopology T') Ab.{u + 1}) 0).obj M)) := by
  let := hπ
  let : PreservesFiniteLimits (smallEtalePushforwardAb π) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom π)).1
  let : PreservesFiniteColimits (smallEtalePushforwardAb π) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom π)).2
  have hc : smallEtaleDerivedPushforwardAbCompIso' π g (π ≫ g) rfl =
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives (smallEtalePushforwardAb π)
        (smallEtalePushforwardAb g) (smallEtalePushforwardAb (π ≫ g))
        (smallEtalePushforwardAbCompIso π g) :=
    congrArg (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives _ _ _)
      (smallEtalePushforwardAbCompIso'_rfl π g)
  rw [hc]
  exact Stacks.DerivedIndexing.collapseIso_comp_rightDerivedIso
    (smallEtalePushforwardAb π) (smallEtalePushforwardAb g) (smallEtalePushforwardAb (π ≫ g))
    (smallEtalePushforwardAbCompIso π g) q M

/-! ### The source side of the degreewise descent -/

/-- The rearrangement that turns the relative Leray identification and one naturality square
into the source side of the descent. Stated on variables in a single abstract category, for the
reason given in the module docstring. -/
public theorem srcChase {𝒞 : Type*} [Category* 𝒞] {o₁ o₂ o₃ o₄ o₅ o₆ : 𝒞}
    {a₁ : o₁ ⟶ o₂} {a₂ : o₂ ⟶ o₃} {b₁ : o₁ ⟶ o₄} {b₂ : o₄ ⟶ o₃}
    {eB : o₃ ⟶ o₅} {eA : o₄ ⟶ o₆} {cc : o₆ ⟶ o₅}
    (h₂ : a₁ ≫ a₂ = b₁ ≫ b₂) (hnat : b₂ ≫ eB = eA ≫ cc) :
    a₁ ≫ a₂ ≫ eB = (b₁ ≫ eA) ≫ cc := by
  rw [← Category.assoc, h₂, Category.assoc, hnat, Category.assoc]

/-- **The source side of the degreewise descent of the direct-image pasting law.** For
`π : T' ⟶ T` integral, `g : T ⟶ S` and `f' : X' ⟶ S`, the inverse image along `f'` of the
relative Leray identification `R^q g_*(π_*ℱ) ⟶ R^q(π ≫ g)_*ℱ`, followed by the identification
`Stacks.EtaleCohomology.baseChangeSourceIso` of the source of the outer rectangle, is the
identification of the source of the lower square at `π_*ℱ`, followed by the degree-`q` cohomology
of the inverse image along `f'` of the comparison of the derived composite direct images.

This is the relative Leray identification read as an edge morphism
(`smallEtaleRelativeLerayIsoOfIntegral_hom_app_comp_rightDerivedIso`) together with the
naturality of `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` for the exact functor
`(f')⁻¹`. -/
public theorem relativeLeray_comp_baseChangeSourceIso {S T X' T' : Scheme.{u}} (f' : X' ⟶ S)
    (g : T ⟶ S) (π : T' ⟶ T) (hπ : IsIntegralHom π) (q : ℕ)
    (M : Sheaf (smallEtaleTopology T') Ab.{u + 1}) :
    (smallEtalePullbackAb f').map
          ((smallEtaleRelativeLerayIsoOfIntegral π g hπ q).hom.app M) ≫
        (baseChangeSourceIso f' (π ≫ g) q).hom.app M =
      (baseChangeSourceIso f' g q).hom.app ((smallEtalePushforwardAb π).obj M) ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
          ((smallEtalePullbackAb f').rightDerivedFunctorPlus.map
            ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.map
                ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
                  (smallEtalePushforwardAb π)).app M) ≫
              (smallEtaleDerivedPushforwardAbCompIso' π g (π ≫ g) rfl).hom.app
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf (smallEtaleTopology T') Ab.{u + 1}) 0).obj M))) := by
  have h₂ := ((smallEtalePullbackAb f').map_comp
        ((smallEtaleRelativeLerayIsoOfIntegral π g hπ q).hom.app M)
        ((Stacks.DerivedIndexing.rightDerivedIso
          (smallEtalePushforwardAb (π ≫ g)) q).hom.app M)).symm.trans
      ((congrArg (smallEtalePullbackAb f').map
          (smallEtaleRelativeLerayIsoOfIntegral_hom_app_comp_rightDerivedIso π g hπ q M)).trans
        ((smallEtalePullbackAb f').map_comp _ _))
  have hnat := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb f') (q : ℤ)).inv.naturality
    ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.map
        ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
          (smallEtalePushforwardAb π)).app M) ≫
      (smallEtaleDerivedPushforwardAbCompIso' π g (π ≫ g) rfl).hom.app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallEtaleTopology T') Ab.{u + 1}) 0).obj M))
  rw [baseChangeSourceIso_hom_app f' (π ≫ g) q M,
    baseChangeSourceIso_hom_app f' g q ((smallEtalePushforwardAb π).obj M)]
  exact srcChase h₂ hnat

end Stacks.EtaleCohomology

end
