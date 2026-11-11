module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# The conormal sheaf of a closed immersion and its functoriality (Stacks 04F7, 01R4)

Let `i : Z ⟶ Z'` be a closed immersion, with ideal sheaf `I = Ker(𝒪_{Z'} ⟶ i_* 𝒪_Z)`. Its
**conormal sheaf** is `𝒞 = i^* I`, a sheaf of `𝒪_Z`-modules; this is the description of
[Stacks Project, Tag 01R1] part (3), and for a first-order thickening — where `I² = 0`, so
`I/I² = I` — it is the sheaf whose pushforward along `i` is `I` itself.

The content of the file is the functoriality of that construction in a commutative square
```
Z --i--→ Z'
|        |
f        k
↓        ↓
W --j--→ W'
```
Because `g ∘ i` factors through `j`, the pullback `k^* J` of the ideal sheaf of `j` maps into `I`
inside `k^* 𝒪_{W'} = 𝒪_{Z'}`, and pulling that map back along `i` and rewriting
`i^* k^* = (i ≫ k)^* = (f ≫ j)^* = f^* j^*` gives
`f^* 𝒞_{W/W'} = f^* j^* J ⟶ i^* I = 𝒞_{Z/Z'}`.
This is the map of [Stacks Project, Tag 01R4] in the case of closed immersions, on all of `Z` and
as a morphism of sheaves of modules rather than of modules of sections.

Specialising to the universal first-order thickenings of two formally unramified morphisms gives
the second assertion of [Stacks Project, Tag 04F7]: the canonical morphism of thickenings of
`Stacks.Thickenings.universalFirstOrderThickeningMap` induces a morphism of conormal sheaves
`f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}`.

## Main definitions

* `Stacks.ClosedImmersion.conormalSheaf` is the conormal sheaf `i^* I` of a morphism of ringed
  spaces.
* `Stacks.ClosedImmersion.idealSheafι` is the inclusion `I ⟶ 𝒪_{Z'}` of the ideal sheaf.
* `Stacks.ClosedImmersion.idealSheafMap` is the morphism `k^* J ⟶ I` of ideal sheaves on `Z'`
  induced by a commutative square.
* `Stacks.ClosedImmersion.pullbackCompIso` is the identification `f^* j^* ≅ i^* k^*` on objects
  furnished by a commutative square.
* `Stacks.ClosedImmersion.conormalSheafMap` is the induced morphism
  `f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}` of conormal sheaves.
* `Stacks.Thickenings.schemeConormalSheaf` is the conormal sheaf of a closed immersion of
  schemes, read on the underlying ringed spaces.
* `Stacks.Thickenings.universalConormalSheafMap` is the morphism of conormal sheaves
  `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04F7].

## Main results

* `Stacks.ClosedImmersion.idealSheafι_comp_structureSheafModuleHom` and
  `Stacks.ClosedImmersion.pullbackIdealSheaf_comp_eq_zero`: the composite
  `k^* J ⟶ 𝒪_{Z'} ⟶ i_* 𝒪_Z` vanishes, which is what makes `idealSheafMap` exist. This is the
  step `g^♯(I') ⊆ I` of the proof of [Stacks Project, Tag 01R4].
* `Stacks.ClosedImmersion.idealSheafMap_comp_ι`: the characterising property of `idealSheafMap`.
  Composed with the inclusion of `I` into `𝒪_{Z'}` it is the pullback along `k` of the inclusion
  of `J` into `𝒪_{W'}`, followed by `k^♯`.
* `Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`: the corresponding description of
  `conormalSheafMap` after mapping both conormal sheaves into `i^* 𝒪_{Z'}`.
* `Stacks.Thickenings.toShHom_universalFirstOrderThickeningMap_inclusion`: the commutative square
  of ringed spaces that the construction is applied to.

## Implementation notes

The ideal sheaf of a closed immersion lives at the level of **ringed spaces**, because that is
where `Stacks.ClosedImmersion.idealSheaf` is defined: it is the categorical kernel of the
structure-sheaf map in `CategoryTheory.SheafOfModules (structureSheafRing Z')`. The whole
construction is therefore carried out for morphisms of ringed spaces and transported to schemes
at the end by `AlgebraicGeometry.Scheme.Hom.toLRSHom` followed by
`AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom`, which is functorial on the nose. In
particular the pullback functor appearing in the statements is
`RingedSpaceModuleAdjunction.modulePullback` on the underlying ringed spaces, not
`AlgebraicGeometry.Scheme.Modules.pullback`. The two describe the same operation, but
`AlgebraicGeometry.Scheme.Modules` carries its own `CategoryTheory.Category` instance whose `Hom`
field is only definitionally — not reducibly — equal to `CategoryTheory.SheafOfModules.Hom`, so
handing a term of one type to a declaration stated for the other makes typeclass resolution, which
unfolds at reducible transparency only, fail. No comparison of the two is proved here, and none is
needed: the ideal sheaf, the conormal sheaf and the morphism between them are all built on the
ringed-space side.

Two steps need care.

The vanishing `k^* J ⟶ 𝒪_{Z'} ⟶ i_* 𝒪_Z = 0` is proved by transposing along `k^* ⊣ k_*`, where
it becomes `J ⟶ 𝒪_{W'} ⟶ (i ≫ k)_* 𝒪_Z = 0`. The cocycle condition
`RingedSpaceModuleAdjunction.structureSheafModuleHom_comp` rewrites the right-hand map as
`𝒪_{W'} ⟶ j_* 𝒪_W ⟶ j_* f_* 𝒪_Z` once `i ≫ k` has been replaced by `f ≫ j`, after which the
vanishing is the defining property of the kernel. That replacement cannot be done by `rw`: the
*type* of `structureSheafModuleHom p` depends on `p`, so the rewrite motive is ill-typed. It is
done instead by generalising the composite to a variable and substituting, which is what
`Stacks.ClosedImmersion.idealSheafι_comp_structureSheafModuleHom` does.

The identification `f^* j^* ≅ i^* k^*` is assembled from
`RingedSpaceModuleAdjunction.modulePullbackComp` on each side and
`RingedSpaceModuleAdjunction.modulePullbackCongr` in the middle. Here the functors
`modulePullback (i ≫ k)` and `modulePullback (f ≫ j)` *do* have the same type, so a genuine
`CategoryTheory.eqToIso` is available; this is the asymmetry with the pushforward side above.

What this file does *not* contain is the comparison of the morphism constructed here with the
affine, module-level conormal map `Stacks.Thickenings.conormalMap` of
`StacksFrontier.AlgebraicGeometry.Thickenings.Conormal`, which sends a section of the defining ideal
of `j` to its image under `k.appTop`. That comparison is the affine characterisation of
[Stacks Project, Tag 01R4] and would be what earns a `01R4` attribute; neither the construction
here nor the one there carries that attribute. The statement of [Stacks Project, Tag 04F7] asks
only for the induced morphism of conormal sheaves, so it does not depend on the comparison.

## References

* [Stacks Project, Tag 01R1](https://stacks.math.columbia.edu/tag/01R1)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction 

universe u

namespace Stacks.ClosedImmersion

variable {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-! ### The conormal sheaf -/

/-- The **conormal sheaf** of a morphism of ringed spaces: the pullback `i^* I` along `i` of the
ideal sheaf `I = Ker(𝒪_{Z'} ⟶ i_* 𝒪_Z)` of `i`, a sheaf of `𝒪_Z`-modules.

For a closed immersion this is the conormal sheaf `𝒞_{Z/Z'}` of [Stacks Project, Tag 01R1] part
(3), whose pushforward along `i` is `I/I²`; for a first-order thickening `I² = 0`, so it is the
sheaf whose pushforward is `I` itself. No hypothesis on `i` is needed to form it. -/
noncomputable abbrev conormalSheaf (i : Z ⟶ Z') : SheafOfModules.{u} (structureSheafRing Z) :=
  (modulePullback i).obj (idealSheaf i)

/-- The inclusion of the ideal sheaf of a morphism of ringed spaces into the structure sheaf of
the target, `I ⟶ 𝒪_{Z'}`.

This is `CategoryTheory.Limits.kernel.ι` of the structure-sheaf map, with its source stated as
`Stacks.ClosedImmersion.idealSheaf i` rather than as a kernel. The two are the same object, but
an unascribed `kernel.ι` forces every composite built from it to be checked against the kernel
spelling, which is not type-correct at `implicit` transparency against the `idealSheaf`
spelling. -/
noncomputable abbrev idealSheafι (i : Z ⟶ Z') :
    idealSheaf i ⟶ SheafOfModules.unit (structureSheafRing Z') :=
  kernel.ι (structureSheafModuleHom i)

/-! ### The ideal sheaf map of a commutative square -/

/-- **A commutative square carries the defining ideal into the defining ideal.** If
`i ≫ k = f ≫ j` then the composite of the inclusion `J ⟶ 𝒪_{W'}` with the structure-sheaf map
`𝒪_{W'} ⟶ (i ≫ k)_* 𝒪_Z` vanishes: by the cocycle condition that map factors as
`𝒪_{W'} ⟶ j_* 𝒪_W ⟶ j_* f_* 𝒪_Z`, and `J` is by definition the kernel of the first factor.

This is the sheaf-level form of `Stacks.Thickenings.mem_ker_appTop_of_comm`, and the step
`g^♯(I') ⊆ I` in the proof of [Stacks Project, Tag 01R4]. -/
theorem idealSheafι_comp_structureSheafModuleHom (comm : i ≫ k = f ≫ j) :
    idealSheafι j ≫ structureSheafModuleHom (i ≫ k) = 0 := by
  have key : ∀ p : Z ⟶ W', p = f ≫ j → idealSheafι j ≫ structureSheafModuleHom p = 0 := by
    rintro p rfl
    have h : kernel.ι (structureSheafModuleHom j) ≫ structureSheafModuleHom j ≫
        (modulePushforward j).map (structureSheafModuleHom f) = 0 := by
      rw [← Category.assoc, kernel.condition, zero_comp]
    exact h
  exact key _ comm

/-- **The pulled-back ideal sheaf is killed by the structure-sheaf map.** The composite
`k^* J ⟶ k^* 𝒪_{W'} ⟶ 𝒪_{Z'} ⟶ i_* 𝒪_Z` vanishes. This is
`Stacks.ClosedImmersion.idealSheafι_comp_structureSheafModuleHom` transposed along the adjunction
`k^* ⊣ k_*`, and is the hypothesis that `Stacks.ClosedImmersion.idealSheafMap` consumes. -/
theorem pullbackIdealSheaf_comp_eq_zero (comm : i ≫ k = f ≫ j) :
    ((modulePullback k).map (idealSheafι j) ≫
        modulePullbackUnitToUnit k) ≫ structureSheafModuleHom i = 0 := by
  refine ((modulePullbackPushforwardAdjunction k).homEquiv _ _).injective ?_
  rw [Category.assoc, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, homEquiv_modulePullbackUnitToUnit,
    ← structureSheafModuleHom_comp]
  refine (idealSheafι_comp_structureSheafModuleHom comm).trans ?_
  rw [Adjunction.homEquiv_unit, modulePushforward_map_zero, comp_zero]
  exact rfl

/-- **The map of ideal sheaves induced by a commutative square.** For `i ≫ k = f ≫ j` the
pullback along `k` of the ideal sheaf of `j` maps canonically to the ideal sheaf of `i`, since
its image in `𝒪_{Z'}` is killed by the structure-sheaf map of `i`. -/
noncomputable def idealSheafMap (comm : i ≫ k = f ≫ j) :
    (modulePullback k).obj (idealSheaf j) ⟶ idealSheaf i :=
  kernel.lift _ _ (pullbackIdealSheaf_comp_eq_zero comm)

/-- **The characterising property of `Stacks.ClosedImmersion.idealSheafMap`.** Followed by the
inclusion of the ideal sheaf of `i` into `𝒪_{Z'}`, it is the pullback along `k` of the inclusion
of the ideal sheaf of `j` into `𝒪_{W'}`, followed by the transpose `k^* 𝒪_{W'} ⟶ 𝒪_{Z'}` of the
structure-sheaf map of `k`.

Since the inclusion of an ideal sheaf is a monomorphism, this determines `idealSheafMap`
uniquely. It is the sheaf-level statement that the induced map is "the one induced by the ring
map `g^♯`" of [Stacks Project, Tag 01R4]. -/
@[simp]
theorem idealSheafMap_comp_ι (comm : i ≫ k = f ≫ j) :
    idealSheafMap comm ≫ idealSheafι i =
      (modulePullback k).map (idealSheafι j) ≫
        modulePullbackUnitToUnit k :=
  kernel.lift_ι _ _ _

/-! ### The conormal sheaf map of a commutative square -/

/-- **The identification `f^* j^* M ≅ i^* k^* M` furnished by a commutative square.** The two
sides are the pullbacks of `M` along the two ways around the square, compared by the composition
law `RingedSpaceModuleAdjunction.modulePullbackComp` on each side and the equality of the
two composites in the middle.

This is the identification `i^* g^* (I'/(I')²) = f^* (i')^* (I'/(I')²)` of the last step of the
proof of [Stacks Project, Tag 01R4]. -/
noncomputable def pullbackCompIso (comm : i ≫ k = f ≫ j)
    (M : SheafOfModules.{u} (structureSheafRing W')) :
    (modulePullback f).obj ((modulePullback j).obj M) ≅
      (modulePullback i).obj ((modulePullback k).obj M) :=
  ((modulePullbackComp f j).app M).symm ≪≫ (modulePullbackCongr comm.symm).app M ≪≫
    (modulePullbackComp i k).app M

/-- **The morphism of conormal sheaves induced by a commutative square**,
`f^* 𝒞_{W/W'} ⟶ 𝒞_{Z/Z'}`: the pullback along `i` of
`Stacks.ClosedImmersion.idealSheafMap`, read through the identification
`f^* j^* ≅ i^* k^*` of `Stacks.ClosedImmersion.pullbackCompIso`.

This is the canonical map of [Stacks Project, Tag 01R4] for closed immersions, on all of `Z` and
as a morphism of sheaves of modules. -/
noncomputable def conormalSheafMap (comm : i ≫ k = f ≫ j) :
    (modulePullback f).obj (conormalSheaf j) ⟶ conormalSheaf i :=
  (pullbackCompIso comm (idealSheaf j)).hom ≫ (modulePullback i).map (idealSheafMap comm)

/-- **The conormal sheaf map is induced by the structure-sheaf map of the ambient morphism.**
After mapping both conormal sheaves into `i^* 𝒪_{Z'}` along the pullbacks of the ideal-sheaf
inclusions, `Stacks.ClosedImmersion.conormalSheafMap` becomes the identification
`f^* j^* ≅ i^* k^*` followed by the pullback along `i` of the characterising composite of
`Stacks.ClosedImmersion.idealSheafMap_comp_ι`.

This is the sheaf-level description of the map that [Stacks Project, Tag 01R4] characterises on
affine charts. -/
theorem conormalSheafMap_comp_pullback_ι (comm : i ≫ k = f ≫ j) :
    conormalSheafMap comm ≫ (modulePullback i).map (idealSheafι i) =
      (pullbackCompIso comm (idealSheaf j)).hom ≫ (modulePullback i).map
        ((modulePullback k).map (idealSheafι j) ≫
          modulePullbackUnitToUnit k) := by
  rw [conormalSheafMap, Category.assoc, ← Functor.map_comp, idealSheafMap_comp_ι]

end Stacks.ClosedImmersion

namespace Stacks.Thickenings

open Stacks.ClosedImmersion

/-! ### The conormal sheaf of a closed immersion of schemes -/

/-- The conormal sheaf of a morphism of schemes, formed on the underlying ringed spaces. For a
closed immersion `i : Z ⟶ Z'` this is `𝒞_{Z/Z'} = i^* I`, where `I` is the defining ideal sheaf
of `i`. -/
noncomputable abbrev schemeConormalSheaf {Z Z' : Scheme.{u}} (i : Z ⟶ Z') :
    SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) :=
  conormalSheaf i.toLRSHom.toShHom

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}

/-- The commutative square of **ringed spaces** underlying
`Stacks.Thickenings.universalFirstOrderThickeningMap_inclusion`: the canonical morphism of
universal first-order thickenings restricts to `f` on the closed subschemes, and passing to
underlying ringed spaces preserves composition on the nose. -/
theorem toShHom_universalFirstOrderThickeningMap_inclusion
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    tZ.inclusion.toLRSHom.toShHom ≫
        (universalFirstOrderThickeningMap tZ tW f g comm).toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ tW.inclusion.toLRSHom.toShHom :=
  congrArg (fun p : Z ⟶ tW.ambient => p.toLRSHom.toShHom)
    (universalFirstOrderThickeningMap_inclusion tZ tW f g comm)

/-- **Stacks 04F7, the conormal half.** Let `h : Z ⟶ X` and `h' : W ⟶ Y` be formally unramified,
let `Z ⊂ Z'` and `W ⊂ W'` be universal first-order thickenings of `h` and of `h'`, and let
`h ≫ g = f ≫ h'` be a commutative square. The canonical morphism `(f, f')` of thickenings of
`Stacks.Thickenings.universalFirstOrderThickeningMap` induces a morphism of conormal sheaves

`f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}`.

It is the map of [Stacks Project, Tag 01R4] applied to the square
`(Z ⊂ Z') → (W ⊂ W')`, namely `Stacks.ClosedImmersion.conormalSheafMap`, which for the
inclusions of thickenings needs no reduction of immersions to closed immersions and no quotient
by the square of the defining ideal. Its characterising property is
`Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`. Read through
`Stacks.Immersion.conormalSheafSelfIso` between the conormal sheaves of
`Stacks.Thickenings.universalConormalSheaf`, it is
`Stacks.Thickenings.universalConormalSheafPullbackMap`, which carries the tag. -/
noncomputable def universalConormalSheafMap
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (f : Z ⟶ W) (g : X ⟶ Y) (comm : h ≫ g = f ≫ h') :
    (modulePullback f.toLRSHom.toShHom).obj (schemeConormalSheaf tW.inclusion) ⟶
      schemeConormalSheaf tZ.inclusion :=
  conormalSheafMap (toShHom_universalFirstOrderThickeningMap_inclusion tZ tW f g comm)

end Stacks.Thickenings

end
