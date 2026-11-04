module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Geometry
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Quasi-compactness and quasi-separatedness in an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces with `W`
quasi-separated, `U` quasi-compact and `V` affine, as in the induction principle of
[Stacks, Tag 08GP]. Then the intersection `P = U ×_W V` is quasi-compact, and the four morphisms
`U ⟶ W`, `V ⟶ W`, `P ⟶ U` and `P ⟶ V` of the square are quasi-compact and quasi-separated, so
that the derived direct images along them preserve quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.Space.mono_edsOpenHom`, `AlgebraicGeometry.Space.mono_edsSnd`: the open
  immersion and its base change are monomorphisms.
* `AlgebraicGeometry.Space.isQuasiCompact_edsOpenHom` and its three companions, and
  `AlgebraicGeometry.Space.isQuasiSeparated_edsOpenHom` and its three companions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The open immersion of an elementary distinguished square is a monomorphism of presheaves. -/
instance mono_edsOpenHom_hom : Mono (edsOpenHom B S hS hsq).hom :=
  inferInstanceAs (Mono Uo.ι)

/-- The open immersion of an elementary distinguished square is a monomorphism. -/
instance mono_edsOpenHom : Mono (edsOpenHom B S hS hsq) :=
  (ObjectProperty.ι _).mono_of_mono_map (mono_edsOpenHom_hom B S hS hsq)

/-- The base change `P ⟶ V` of the open immersion is a monomorphism of presheaves. -/
instance mono_edsSnd_hom : Mono (edsSnd B S hS hsq).hom :=
  inferInstanceAs (Mono (pullback.snd (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom))

/-- The base change `P ⟶ V` of the open immersion is a monomorphism. -/
instance mono_edsSnd : Mono (edsSnd B S hS hsq) :=
  (ObjectProperty.ι _).mono_of_mono_map (mono_edsSnd_hom B S hS hsq)

/-- The open immersion of an elementary distinguished square is quasi-separated. -/
theorem isQuasiSeparated_edsOpenHom : IsQuasiSeparated B S hS (edsOpenHom B S hS hsq).hom :=
  isQuasiSeparated_of_mono B S hS _ inferInstance

/-- The base change `P ⟶ V` of the open immersion is quasi-separated. -/
theorem isQuasiSeparated_edsSnd : IsQuasiSeparated B S hS (edsSnd B S hS hsq).hom :=
  isQuasiSeparated_of_mono B S hS _ inferInstance

variable {hsq}

/-- The étale morphism of the square is quasi-separated as soon as `V` is quasi-separated. -/
theorem isQuasiSeparated_edsEtaleHom (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V) :
    IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq).hom :=
  isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hsq.isAlgebraicSpace hVqs _

/-- The projection `P ⟶ U` is quasi-separated as soon as `V` is quasi-separated, being a base
change of `V ⟶ W`. -/
theorem isQuasiSeparated_edsFst (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V) :
    IsQuasiSeparated B S hS (edsFst B S hS hsq).hom :=
  isQuasiSeparated_of_isPullback B S hS
    (Functor.map_isPullback (ObjectProperty.ι _) (isPullback_edsInter B S hS hsq)).flip
    (isQuasiSeparated_edsEtaleHom (hsq := hsq) B S hS hZ hVqs)

/-- The open subspace of the square is quasi-separated when `W` is. -/
theorem isAbsolutelyQuasiSeparated_edsOpen (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) :
    IsAbsolutelyQuasiSeparated B S hS hZ (edsOpen B S hS hsq).1 :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (edsOpen B S hS hsq).2 hWqs
    (isQuasiSeparated_edsOpenHom B S hS hsq)

/-- The open immersion of the square is quasi-compact when `U` is quasi-compact and `W` is
quasi-separated. -/
theorem isQuasiCompact_edsOpenHom (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor) :
    IsQuasiCompact B S hS (edsOpenHom B S hS hsq).hom :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hUqc _

/-- The étale morphism of the square is quasi-compact when `V` is quasi-compact and `W` is
quasi-separated. -/
theorem isQuasiCompact_edsEtaleHom (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hVqc : IsQuasiCompactSpace B S hS V) :
    IsQuasiCompact B S hS (edsEtaleHom B S hS hsq).hom :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hVqc _

/-- The projection `P ⟶ V` is quasi-compact when `P` is quasi-compact and `V` quasi-separated. -/
theorem isQuasiCompact_edsSnd (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V)
    (hPqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1) :
    IsQuasiCompact B S hS (edsSnd B S hS hsq).hom :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hsq.isAlgebraicSpace hVqs hPqc _

/-- The projection `P ⟶ U` is quasi-compact when `P` is quasi-compact and `W` quasi-separated. -/
theorem isQuasiCompact_edsFst (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hPqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1) :
    IsQuasiCompact B S hS (edsFst B S hS hsq).hom :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (edsOpen B S hS hsq).2
    (isAbsolutelyQuasiSeparated_edsOpen B S hS hZ hWqs) hPqc _

end AlgebraicGeometry.Space

end
